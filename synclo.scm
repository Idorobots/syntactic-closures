(define *gensym-counter* 0)
(define (gensym root)
  (set! *gensym-counter* (+ 1 *gensym-counter*))
  (string->symbol
   (string-append (symbol->string root)
                  (number->string *gensym-counter*))))

(define-struct syntactic-closure (syntactic-env free-names exp) #:transparent)

(define (make-syntactic-closure-list syntactic-env free-names exps)
  (map (lambda (exp)
         (make-syntactic-closure syntactic-env free-names exp))
       exps))

(define (execute code)
  (eval code))

(define null-syntactic-environment '())

(define core-syntactic-environment null-syntactic-environment)

(define (extend-syntactic-environment outer-env keyword expander)
  (cons (cons keyword expander)
        outer-env))

(define (add-identifier outer-env identifier)
  (let ((variable (gensym identifier)))
    (extend-syntactic-environment outer-env identifier variable)))

(define (add-identifier-list syntactic-env identifiers)
  (if (null? identifiers)
      syntactic-env
      (add-identifier (add-identifier-list syntactic-env
                                           (cdr identifiers))
                      (car identifiers))))

(define (filter-syntactic-environment names names-syntactic-env else-syntactic-env)
  (append (filter (lambda (expander)
                    (memq (car expander) names))
                  names-syntactic-env)
          else-syntactic-env))

(define (syntactic-environment-def syntactic-env keyword)
  (assoc keyword syntactic-env))

(define (expand syntactic-env exp)
  ((cond ((syntactic-closure? exp) expand-syntactic-closure)
         ((symbol? exp) expand-symbol)
         ((not (pair? exp)) expand-constant)
         (else (case (car exp)
                 ((quote) expand-quote)
                 ((if begin set!) expand-simple)
                 ((lambda) expand-lambda)
                 (else expand-application))))
   syntactic-env
   exp))

(define (expand-list syntactic-env exps)
  (map (lambda (exp)
         (expand syntactic-env exp))
       exps))

(define (expand-symbol syntactic-env exp)
  (let ((def (syntactic-environment-def syntactic-env exp)))
    (if def
        (if (expander? (cdr def))
            ;; FIXME Should this expand symbols here?
            (expand-expander (cdr def) syntactic-env exp)
            (cdr def))
        (expand-free-variable syntactic-env exp))))

(define (expand-application syntactic-env exp)
  (let* ((op (car exp))
         (def (syntactic-environment-def syntactic-env op)))
    (if def
        (if (expander? (cdr def))
            (expand-expander (cdr def) syntactic-env exp)
            ;; NOTE Originally the cdr is expanded in the outer env.
            (expand-combination syntactic-env exp))
        (expand-combination syntactic-env exp))))

(define (expander? x)
  (procedure? x))

(define (expand-expander expander syntactic-env exp)
  ;; FIXME This ought to error out if expansion of the expander-produced code contains free-vars.
  (expand null-syntactic-environment
          (expander syntactic-env exp)))

(define (expand-constant syntactic-env exp)
  exp)

(define (expand-quote syntactic-env exp)
  ;; FIXME This currently doesn't expand embedded unquotes.
  exp)

(define (expand-free-variable syntactic-env exp)
  exp)

(define (expand-combination syntactic-env exp)
  `(,@(expand-list syntactic-env exp)))

(define (expand-simple syntactic-env exp)
  `(,(car exp) ,@(expand-list syntactic-env (cdr exp))))

(define (expand-lambda syntactic-env exp)
  (let ((syntactic-env (add-identifier-list syntactic-env
                                            (cadr exp))))
    `(lambda ,(expand-list syntactic-env (cadr exp))
       ,@(expand-list syntactic-env (cddr exp)))))

(define (expand-syntactic-closure free-names-syntactic-env syntactic-closure)
  (expand (filter-syntactic-environment (syntactic-closure-free-names syntactic-closure)
                                        free-names-syntactic-env
                                        (syntactic-closure-syntactic-env syntactic-closure))
          (syntactic-closure-exp syntactic-closure)))

(define (let-expander syntactic-env exp)
  (let ((identifiers (map car (cadr exp))))
    (make-syntactic-closure scheme-syntactic-environment '()
                            `((lambda ,identifiers
                                ,@(make-syntactic-closure-list
                                   syntactic-env identifiers
                                   (cddr exp)))
                              ,@(make-syntactic-closure-list
                                 syntactic-env '()
                                 (map cadr (cadr exp)))))))

(define (delay-expander syntactic-env exp)
  (let ((delayed (make-syntactic-closure syntactic-env '()
                                         (cadr exp))))
    (make-syntactic-closure scheme-syntactic-environment '()
                            `(make-promise (lambda () ,delayed)))))

(define (and-expander syntactic-env exp)
  (let ((operands (make-syntactic-closure-list
                   syntactic-env '()
                   (cdr exp))))
    (cond ((null? operands)
           (make-syntactic-closure scheme-syntactic-environment '() '#t))
          ((null? (cdr operands))
           (car operands))
          (else
           (make-syntactic-closure scheme-syntactic-environment '()
                                   `(let ((temp ,(car operands)))
                                      (if temp
                                          (and ,@(cdr operands))
                                          temp)))))))

(define (or-expander syntactic-env exp)
  (let ((operands (make-syntactic-closure-list
                   syntactic-env '()
                   (cdr exp))))
    (cond ((null? operands)
           (make-syntactic-closure scheme-syntactic-environment '() '#f))
          ((null? (cdr operands))
           (car operands))
          (else
           (make-syntactic-closure scheme-syntactic-environment '()
                                   `(let ((temp ,(car operands)))
                                      (if temp
                                          temp
                                          (or ,@(cdr operands)))))))))

(define (cond-expander syntactic-env exp)
  (define (process-cond-clauses syntactic-env clauses)
    (let ((body (make-syntactic-closure-list syntactic-env '() (cdar clauses))))
      (cond ((not (null? (cdr clauses)))
             (let ((test (make-syntactic-closure
                          syntactic-env '()
                          (caar clauses)))
                   (rest (process-cond-clauses syntactic-env
                                               (cdr clauses))))
               (if (null? body)
                   `(or ,test ,rest)
                   `(if ,test
                        (begin ,@body)
                        ,rest))))
            ((eq? (caar clauses) 'else)
             `(begin ,@body))
            (else
             (let ((test (make-syntactic-closure
                          syntactic-env '()
                          (caar clauses))))
               (if (null? body)
                   test
                   `(if ,test
                        (begin ,@body))))))))
  (make-syntactic-closure scheme-syntactic-environment '()
                          (process-cond-clauses syntactic-env (cdr exp))))

(define (case-expander syntactic-env exp)
  (define (process-case-clauses syntactic-env clauses)
    (let ((data (caar clauses))
          (body (make-syntactic-closure-list
                 syntactic-env '()
                 (cdar clauses))))
      (cond ((not (null? (cdr clauses)))
             (let ((rest (process-case-clauses
                          syntactic-env (cdr clauses))))
               `(if (memv temp ',data)
                    (begin ,@body)
                    ,rest)))
            ((eq? data 'else)
             `(begin ,@body))
            (else
             `(if (memv temp ',data)
                  (begin ,@body))))))
  (make-syntactic-closure scheme-syntactic-environment '()
                          `(let ((temp ,(make-syntactic-closure syntactic-env '()
                                                                (cadr exp))))
                             ,(process-case-clauses syntactic-env (cddr exp)))))

(define (with-macro-expander with-macro-syntactic-env exp)
  (let* ((keyword (caadr exp))
         (transformer (execute
                       (expand scheme-syntactic-environment
                               `(lambda ,(cdadr exp)
                                  ,(caddr exp)))))
         (expander (lambda (syntactic-env exp)
                     (make-syntactic-closure
                      with-macro-syntactic-env '()
                      (apply transformer
                             (make-syntactic-closure-list
                              syntactic-env '()
                              (cdr exp)))))))
    (make-syntactic-closure scheme-syntactic-environment '()
                            `(begin
                               ,@(make-syntactic-closure-list
                                  (extend-syntactic-environment
                                   with-macro-syntactic-env
                                   keyword
                                   expander)
                                  '()
                                  (cdddr exp))))))

(define (with-macro-rec-expander with-macro-syntactic-env exp)
  (let* ((keyword (caadr exp))
         (transformer (execute
                       (expand scheme-syntactic-environment
                               `(lambda ,(cdadr exp)
                                  ,(caddr exp)))))
         (extended-syntactic-env #f)
         (expander (lambda (syntactic-env exp)
                     (make-syntactic-closure
                      extended-syntactic-env '()
                      (apply transformer
                             (make-syntactic-closure-list
                              syntactic-env '()
                              (cdr exp)))))))
    (set! extended-syntactic-env
          (extend-syntactic-environment
           with-macro-syntactic-env
           keyword
           expander))
    (make-syntactic-closure scheme-syntactic-environment '()
                            `(begin
                               ,@(make-syntactic-closure-list
                                  extended-syntactic-env '()
                                  (cdddr exp))))))

(define scheme-syntactic-environment
  (foldl (lambda (expander syntactic-env)
           (extend-syntactic-environment
            syntactic-env
            (car expander)
            (cadr expander)))
         core-syntactic-environment
         (list (list 'delay delay-expander)
               (list 'or or-expander)
               (list 'and and-expander)
               (list 'let let-expander)
               (list 'cond cond-expander)
               (list 'case case-expander)
               (list 'with-macro with-macro-expander)
               (list 'with-macro-rec with-macro-rec-expander))))

(expand scheme-syntactic-environment
        '(begin
           (cond ((or (something? x)
                      (something-else? y))
                  do this stuff)
                 ((otherwise?)
                  (let ((x 23))
                    (* x x)))
                 (else
                  23))
           (case 23
             ((23) #t)
             ((5 7 13) 'nope)
             (else
              ':shrug:))
           (lambda (let*)
             (let ((a b))
               c))
           (lambda (let)
             (let ((a b))
               c))
           (with-macro (let x y)
                       `(begin
                          (display "letting ")
                          (display ,x)
                          (display " to do ")
                          (display ,y)
                          (newline))
                       (lambda (let)
                         (let ((a b))
                           c)))
           (with-macro (let x y)
                       `(begin
                          (display "letting ")
                          (display ,x)
                          (display " to do ")
                          (display ,y)
                          (newline))
                       (lambda (let*)
                         (let ((a b))
                           c)))
           (display "wut")))
