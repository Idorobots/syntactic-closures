;; Gensym:

(define *gensym-counter* 0)
(define (gensym root)
  (set! *gensym-counter* (+ 1 *gensym-counter*))
  (string->symbol
   (string-append (symbol->string root)
                  (number->string *gensym-counter*))))

;; Syntactic closures:

(define-struct syntactic-closure (env free-names exp) #:transparent)

(define (make-syntactic-closure-list env free-names exps)
  (map (lambda (exp)
         (make-syntactic-closure env free-names exp))
       exps))

;; Syntactic environments:

(define core-syntactic-environment '())

(define (extend-syntactic-environment outer-env keyword expander)
  (cons (cons keyword expander)
        outer-env))

(define (add-identifier outer-env identifier)
  (let ((variable (gensym identifier)))
    (extend-syntactic-environment outer-env identifier variable)))

(define (add-identifier-list env identifiers)
  (if (null? identifiers)
      env
      (add-identifier (add-identifier-list env
                                           (cdr identifiers))
                      (car identifiers))))

(define (identifier=? env1 id1 env2 id2)
  (let ((first (syntactic-environment-def env1 id1))
        (second (syntactic-environment-def env2 id2)))
    (and first
         second
         (equal? first second))))

(define (filter-syntactic-environment names names-syntactic-env else-syntactic-env)
  (append (filter (lambda (expander)
                    (memq (car expander) names))
                  names-syntactic-env)
          else-syntactic-env))

(define (syntactic-environment-def env keyword)
  (assoc keyword env))

;; Interpreter:

(define (execute exp env)
  (cond ((syntactic-closure? exp)
         (make-syntactic-closure (syntactic-closure-env exp)
                                 (syntactic-closure-free-names exp)
                                 (execute (syntactic-closure-exp exp)
                                          env)))
        ((symbol? exp)
         (let ((def (syntactic-environment-def env exp)))
           (if (and def
                    (not (expander? (cdr def))))
               (cdr def)
               (error "Undefined variable" exp))))
        ((not (pair? exp))
         exp)
        (else (case (car exp)
                ((quote)
                 (cadr exp))
                ((if)
                 (if (execute (cadr exp) env)
                     (execute (caddr exp) env)
                     (execute (cadddr exp) env)))
                ((begin)
                 (last (map (lambda (expr)
                              (execute expr env))
                            (cdr exp))))
                ((set!)
                 (let ((def (syntactic-environment-def env (cadr exp))))
                   (if def
                       (set-cdr! def (execute (caddr exp) env))
                       (error "Undefined variable" (cadr exp)))))
                ((lambda)
                 (let ((formals (cadr exp))
                       (body (cddr exp)))
                   (lambda args
                     (if (equal? (length args)
                                 (length formals))
                         (let ((extended-env (foldl (lambda (binding env)
                                                      (extend-syntactic-environment env (car binding) (cdr binding)))
                                                    env
                                                    (map cons
                                                         formals
                                                         args))))
                           (last (map (lambda (expr)
                                        (execute expr extended-env))
                                      body)))
                         (error "Arity mismatch" (length args))))))
                (else
                 (apply (execute (car exp) env)
                        (map (lambda (arg)
                               (execute arg env))
                             (cdr exp))))))))

(define (sc-macro-transformer f)
  (lambda (expr use-env def-env)
    (make-syntactic-closure def-env '() (f expr def-env))))

(define (rsc-macro-transformer f)
  (lambda (expr use-env def-env)
    (f expr def-env)))

(define (er-macro-transformer f)
  (lambda (expr use-env def-env)
    (let ((renames '()))
      (f expr
         (lambda (identifier)
           (let ((renamed (assq identifier renames)))
             (if renamed
                 (cdr renamed)
                 (let ((name (make-syntactic-closure def-env '() identifier)))
                   (set! renames (cons (cons identifier name)))
                   name))))
         (lambda (x y)
           (identifier=? use-env x use-env y))))))

(define core-interpretation-environment
  (list (cons 'null? null?)
        (cons 'cons cons)
        (cons 'car car)
        (cons 'cdr cdr)
        (cons 'list list)
        (cons 'cadr cadr)
        (cons 'cddr cddr)
        (cons 'make-syntactic-closure make-syntactic-closure)
        (cons 'identifier=? identifier=?)
        (cons 'sc-macro-transformer sc-macro-transformer)
        (cons 'rsc-macro-transformer rsc-macro-transformer)
        (cons 'er-macro-transformer er-macro-transformer)))

;; Macro-expansion:

(define (expand env exp)
  ((cond ((syntactic-closure? exp) expand-syntactic-closure)
         ((symbol? exp) expand-symbol)
         ((not (pair? exp)) expand-constant)
         (else (case (car exp)
                 ((quote) expand-quote)
                 ((if begin set!) expand-simple)
                 ((lambda) expand-lambda)
                 (else expand-application))))
   env
   exp))

(define (expand-list env exps)
  (map (lambda (exp)
         (expand env exp))
       exps))

(define (expand-symbol env exp)
  (let ((def (syntactic-environment-def env exp)))
    (if def
        (if (expander? (cdr def))
            ;; FIXME Should this expand symbols here?
            (expand-expander (cdr def) env exp)
            (cdr def))
        (expand-free-variable env exp))))

(define (expand-application env exp)
  (let* ((op (car exp))
         (def (syntactic-environment-def env op)))
    (if def
        (if (expander? (cdr def))
            (expand-expander (cdr def) env exp)
            ;; NOTE Originally the cdr is expanded in the outer env.
            (expand-combination env exp))
        (expand-combination env exp))))

(define (expand-expander expander env exp)
  ;; FIXME This now matches the behaviour from the original paper. Not sure if this is desirable.
  (let ((value ((expander-proc expander) exp env (expander-env expander))))
    (if (syntactic-closure? value)
        (expand-syntactic-closure env value)
        (error "Unescaped value" exp))))

(define (expand-constant env exp)
  exp)

(define (expand-quote env exp)
  (if (syntactic-closure? (cadr exp))
      `(quote ,(syntactic-closure-exp (cadr exp)))
      exp))

(define (expand-free-variable env exp)
  exp)

(define (expand-combination env exp)
  `(,@(expand-list env exp)))

(define (expand-simple env exp)
  `(,(car exp) ,@(expand-list env (cdr exp))))

(define (expand-lambda env exp)
  (let ((env (add-identifier-list env
                                  (cadr exp))))
    `(lambda ,(expand-list env (cadr exp))
       ,@(expand-list env (cddr exp)))))

(define (expand-syntactic-closure free-names-syntactic-env exp)
  (expand (filter-syntactic-environment (syntactic-closure-free-names exp)
                                        free-names-syntactic-env
                                        (syntactic-closure-env exp))
          (syntactic-closure-exp exp)))

;; Expanders:

(define-struct expander ((env #:mutable) proc))

(define let-expander
  (lambda (exp env def-env)
    (let ((identifiers (map car (cadr exp))))
      (make-syntactic-closure def-env '()
                              `((lambda ,identifiers
                                  ,@(make-syntactic-closure-list
                                     env identifiers
                                     (cddr exp)))
                                ,@(make-syntactic-closure-list
                                   env '()
                                   (map cadr (cadr exp))))))))

(define delay-expander
  (lambda (exp env def-env)
    (let ((delayed (make-syntactic-closure env '()
                                           (cadr exp))))
      (make-syntactic-closure def-env '()
                              `(make-promise (lambda () ,delayed))))))

(define and-expander
  (lambda (exp env def-env)
    (let ((operands (make-syntactic-closure-list
                     env '()
                     (cdr exp))))
      (cond ((null? operands)
             (make-syntactic-closure def-env '() '#t))
            ((null? (cdr operands))
             (car operands))
            (else
             (make-syntactic-closure def-env '()
                                     `(let ((temp ,(car operands)))
                                        (if temp
                                            (and ,@(cdr operands))
                                            temp))))))))

(define or-expander
  (lambda (exp env def-env)
    (let ((operands (make-syntactic-closure-list
                     env '()
                     (cdr exp))))
      (cond ((null? operands)
             (make-syntactic-closure def-env '() '#f))
            ((null? (cdr operands))
             (car operands))
            (else
             (make-syntactic-closure def-env '()
                                     `(let ((temp ,(car operands)))
                                        (if temp
                                            temp
                                            (or ,@(cdr operands))))))))))

(define cond-expander
  (lambda (exp env def-env)
    (define (process-cond-clauses env clauses)
      (let ((body (make-syntactic-closure-list env '() (cdar clauses))))
        (cond ((not (null? (cdr clauses)))
               (let ((test (make-syntactic-closure
                            env '()
                            (caar clauses)))
                     (rest (process-cond-clauses env
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
                            env '()
                            (caar clauses))))
                 (if (null? body)
                     test
                     `(if ,test
                          (begin ,@body))))))))
    (make-syntactic-closure def-env '()
                            (process-cond-clauses env (cdr exp)))))

(define case-expander
  (lambda (exp env def-env)
    (define (process-case-clauses env clauses)
      (let ((data (caar clauses))
            (body (make-syntactic-closure-list
                   env '()
                   (cdar clauses))))
        (cond ((not (null? (cdr clauses)))
               (let ((rest (process-case-clauses
                            env (cdr clauses))))
                 `(if (memv temp ',data)
                      (begin ,@body)
                      ,rest)))
              ((eq? data 'else)
               `(begin ,@body))
              (else
               `(if (memv temp ',data)
                    (begin ,@body))))))
    (make-syntactic-closure def-env '()
                            `(let ((temp ,(make-syntactic-closure env '()
                                                                  (cadr exp))))
                               ,(process-case-clauses env (cddr exp))))))

(define with-macro-expander
  (lambda (exp with-macro-env def-env)
    (let* ((keyword (caadr exp))
           (transformer (execute
                         (expand def-env
                                 `(lambda ,(cdadr exp)
                                    ,(caddr exp)))
                         core-interpretation-environment))
           (expander (make-expander with-macro-env
                                    (lambda (exp env def-env)
                                      (make-syntactic-closure
                                       def-env '()
                                       (apply transformer
                                              (make-syntactic-closure-list
                                               env '()
                                               (cdr exp))))))))
      (make-syntactic-closure def-env '()
                              `(begin
                                 ,@(make-syntactic-closure-list
                                    (extend-syntactic-environment
                                     with-macro-env
                                     keyword
                                     expander)
                                    '()
                                    (cdddr exp)))))))

(define with-macro-rec-expander
  (lambda (exp with-macro-env def-env)
    (let* ((keyword (caadr exp))
           (transformer (execute
                         (expand def-env
                                 `(lambda ,(cdadr exp)
                                    ,(caddr exp)))
                         core-interpretation-environment))
           (extended-env #f)
           (expander (make-expander extended-env
                                    (lambda (exp env def-env)
                                      (make-syntactic-closure
                                       def-env '()
                                       (apply transformer
                                              (make-syntactic-closure-list
                                               env '()
                                               (cdr exp))))))))
      (set! extended-env
            (extend-syntactic-environment
             with-macro-env
             keyword
             expander))
      (make-syntactic-closure def-env '()
                              `(begin
                                 ,@(make-syntactic-closure-list
                                    extended-env '()
                                    (cdddr exp)))))))

(define quasiquote-expander
  (lambda (exp env def-env)
    (define (mse expr)
      (make-syntactic-closure env '()
                              expr))
    (let* ((body (cadr exp)))
      (make-syntactic-closure
       def-env '()
       (cond ((or (null? body)
                  (symbol? body))
              `(quote ,(mse body)))
             ((and (pair? body)
                   (eq? (car body) 'unquote))
              (mse (cadr body)))
             ((pair? body)
              `(cons
                ,(mse (list 'quasiquote (car body)))
                ,(mse (list 'quasiquote (cdr body)))))
             (else
              body))))))

;; Global syntactic env:

(define scheme-syntactic-environment
  (foldl (lambda (expander env)
           (extend-syntactic-environment
            env
            (car expander)
            (make-expander #f ;; NOTE This will be adjusted shortly.
                           (cadr expander))))
         core-syntactic-environment
         (list (list 'delay delay-expander)
               (list 'or or-expander)
               (list 'and and-expander)
               (list 'let let-expander)
               (list 'cond cond-expander)
               (list 'case case-expander)
               (list 'with-macro with-macro-expander)
               (list 'with-macro-rec with-macro-rec-expander)
               (list 'quasiquote quasiquote-expander))))

(map (lambda (b)
       (if (expander? (cdr b))
           (set-expander-env! (cdr b)
                              scheme-syntactic-environment)
           b))
     scheme-syntactic-environment)

;; Example:

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
                          (display ',x)
                          (display " to do ")
                          (display ',y)
                          (newline))
                       (lambda (let)
                         (let ((a b))
                           c)))
           (with-macro (let x y)
                       `(begin
                          (display "letting ")
                          (display ',x)
                          (display " to do ")
                          (display ',y)
                          (newline))
                       (lambda (let*)
                         (let ((a b))
                           c)))
           (display `(list ,(+ 2 2) "wut"))))
