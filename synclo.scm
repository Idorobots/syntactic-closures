(define *gensym-counter* 0)
(define (gensym root)
  (set! *gensym-counter* (+ 1 *gensym-counter*))
  (string->symbol
   (string-append (symbol->string root)
                  (number->string *gensym-counter*))))

(define (execute code)
  (eval code))

(define (compile syntactic-env exp)
  (syntactic-env syntactic-env exp))

(define (compile-list syntactic-env exps)
  (map (lambda (exp)
         (syntactic-env syntactic-env exp))
       exps))

(define (extend-syntactic-environment outer-syntactic-env keyword expander)
  (lambda (syntactic-env exp)
    (if (and (pair? exp)
             (eq? (car exp) keyword))
        (compile null-syntactic-environment
                 (expander syntactic-env exp))
        (outer-syntactic-env syntactic-env exp))))

(define (add-identifier-list syntactic-env identifiers)
  (if (null? identifiers)
      syntactic-env
      (add-identifier (add-identifier-list syntactic-env
                                           (cdr identifiers))
                      (car identifiers))))

(define (add-identifier outer-syntactic-env identifier)
  (let ((variable (gensym identifier)))
    (lambda (syntactic-env exp)
      (if (eq? exp identifier)
          variable
          (outer-syntactic-env syntactic-env exp)))))

(define (filter-syntactic-env names names-syntactic-env else-syntactic-env)
  (lambda (syntactic-env exp)
    ((if (memq (if (pair? exp)
                   (car exp)
                   exp)
               names)
         names-syntactic-env
         else-syntactic-env)
     syntactic-env
     exp)))

(define (null-syntactic-environment syntactic-env exp)
  (if (syntactic-closure? exp)
      (compile-syntactic-closure syntactic-env exp)
      (error (list "Unclosed expression:" exp))))

(define (core-syntactic-environment syntactic-env exp)
  ((cond ((syntactic-closure? exp) compile-syntactic-closure)
         ((symbol? exp) compile-free-variable)
         ((not (pair? exp)) compile-constant)
         (else (case (car exp)
                 ((quote) compile-constant)
                 ((if begin set!) compile-simple)
                 ((lambda) compile-lambda)
                 (else compile-combination))))
   syntactic-env
   exp))

(define (compile-constant syntactic-env exp)
  exp)

(define (compile-free-variable syntactic-env exp)
  exp)

(define (compile-combination syntactic-env exp)
  `(,@(compile-list syntactic-env exp)))

(define (compile-simple syntactic-env exp)
  `(,(car exp) ,@(compile-list syntactic-env (cdr exp))))

(define (compile-lambda syntactic-env exp)
  (let ((syntactic-env (add-identifier-list syntactic-env
                                            (cadr exp))))
    `(lambda ,(compile-list syntactic-env (cadr exp))
       ,@(compile-list syntactic-env (cddr exp)))))

(define (make-syntactic-closure syntactic-env free-names exp)
  (vector 'syntactic-closure
          (lambda (free-names-syntactic-env)
            (compile (filter-syntactic-env free-names free-names-syntactic-env syntactic-env)
                     exp))))

(define (make-syntactic-closure-list syntactic-env free-names exps)
  (map (lambda (exp)
         (make-syntactic-closure syntactic-env free-names exp))
       exps))

(define (syntactic-closure? x)
  (and (vector? x)
       (= 2 (vector-length x))
       (eq? 'syntactic-closure (vector-ref x 0))))

(define (compile-syntactic-closure syntactic-env syntactic-closure)
  ((vector-ref syntactic-closure 1) syntactic-env))

(define (scheme-macrology base-syntactic-env)
  (define (let-expander syntactic-env exp)
    (let ((identifiers (map car (cadr exp))))
      (make-syntactic-closure final-syntactic-env '()
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
      (make-syntactic-closure final-syntactic-env '()
                              `(make-promise (lambda () ,delayed)))))

  (define (and-expander syntactic-env exp)
    (let ((operands (make-syntactic-closure-list
                     syntactic-env '()
                     (cdr exp))))
      (cond ((null? operands)
             (make-syntactic-closure final-syntactic-env '() '#t))
            ((null? (cdr operands))
             (car operands))
            (else
             (make-syntactic-closure final-syntactic-env '()
                                     `(let ((temp ,(car operands)))
                                        (if temp
                                            (and ,@(cdr operands))
                                            temp)))))))

  (define (or-expander syntactic-env exp)
    (let ((operands (make-syntactic-closure-list
                     syntactic-env '()
                     (cdr exp))))
      (cond ((null? operands)
             (make-syntactic-closure final-syntactic-env '() '#f))
            ((null? (cdr operands))
             (car operands))
            (else
             (make-syntactic-closure final-syntactic-env '()
                                     `(let ((temp ,(car operands)))
                                        (if temp
                                            temp
                                            (or ,@(cdr operands)))))))))

  (define (cond-expander syntactic-env exp)
    (make-syntactic-closure final-syntactic-env '()
                            (process-cond-clauses syntactic-env (cdr exp))))

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

  (define (case-expander syntactic-env exp)
    (make-syntactic-closure final-syntactic-env '()
                            `(let ((temp ,(make-syntactic-closure syntactic-env '()
                                                                  (cadr exp))))
                               ,(process-case-clauses syntactic-env (cddr exp)))))

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

  (define (with-macro-expander with-macro-syntactic-env exp)
    (let* ((keyword (caadr exp))
           (transformer (execute
                         (compile scheme-syntactic-environment
                                  `(lambda ,(cdadr exp)
                                     ,(caddr exp)))))
           (expander (lambda (syntactic-env exp)
                       (make-syntactic-closure
                        with-macro-syntactic-env '()
                        (apply transformer
                               (make-syntactic-closure-list
                                syntactic-env '()
                                (cdr exp)))))))
      (make-syntactic-closure final-syntactic-env '()
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
                         (compile scheme-syntactic-environment
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
      (make-syntactic-closure final-syntactic-env '()
                              `(begin
                                 ,@(make-syntactic-closure-list
                                    extended-syntactic-env '()
                                    (cdddr exp))))))

  (define final-syntactic-env #f)

  (do ((syntactic-env base-syntactic-env
                      (extend-syntactic-environment
                       syntactic-env
                       (caar pairs)
                       (cadar pairs)))
       (pairs (list (list 'delay delay-expander)
                    (list 'or or-expander)
                    (list 'and and-expander)
                    (list 'let let-expander)
                    (list 'cond cond-expander)
                    (list 'case case-expander)
                    (list 'with-macro with-macro-expander)
                    (list 'with-macro-rec with-macro-rec-expander))
              (cdr pairs)))
      ((null? pairs)
       (set! final-syntactic-env syntactic-env)))

  final-syntactic-env)

(define scheme-syntactic-environment
  (scheme-macrology core-syntactic-environment))

(compile scheme-syntactic-environment
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
