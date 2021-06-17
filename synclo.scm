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
    (make-syntactic-closure def-env '()
                            (f expr use-env))))

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
        (cons 'caddr caddr)
        (cons 'cddr cddr)
        (cons 'cdddr cdddr)
        (cons 'make-syntactic-closure make-syntactic-closure)
        (cons 'identifier=? identifier=?)
        (cons 'sc-macro-transformer sc-macro-transformer)
        (cons 'rsc-macro-transformer rsc-macro-transformer)
        (cons 'er-macro-transformer er-macro-transformer)))

;; Macro-expansion:

(define (expand env exp cont)
  ((cond ((syntactic-closure? exp) expand-syntactic-closure)
         ((symbol? exp) expand-symbol)
         ((not (pair? exp)) expand-constant)
         (else (case (car exp)
                 ((quote) expand-quote)
                 ((if begin set!) expand-simple)
                 ((lambda) expand-lambda)
                 (else expand-application))))
   env
   exp
   cont))

(define (expand-constant env exp cont)
  (cont env exp))

(define (expand-quote env exp cont)
  (cont env
        (if (syntactic-closure? (cadr exp))
            `(quote ,(syntactic-closure-exp (cadr exp)))
            exp)))

(define (expand-free-variable env exp cont)
  (cont env exp))

(define (expand-symbol env exp cont)
  (let ((def (syntactic-environment-def env exp)))
    (if def
        (if (expander? (cdr def))
            ;; FIXME Should this expand symbols here?
            (expand-expander (cdr def) env exp cont)
            (cont env (cdr def)))
        (expand-free-variable env exp cont))))

(define (expand-application env exp cont)
  (let* ((op (car exp))
         (def (syntactic-environment-def env op)))
    (if def
        (if (expander? (cdr def))
            (expand-expander (cdr def) env exp cont)
            ;; NOTE Originally the cdr is expanded in the outer env.
            (expand-combination env exp cont))
        (expand-combination env exp cont))))

(define (expand-expander expander env exp cont)
  ;; FIXME This now matches the behaviour from the original paper. Not sure if this is desirable.
  (let ((value ((expander-proc expander) exp env (expander-env expander))))
    (if (syntactic-closure? value)
        (expand-syntactic-closure env value cont)
        (error "Unescaped value" value))))

(define (expand-combination env exp cont)
  (expand-list env exp
               (lambda (env expanded)
                 (cont env `(,@expanded)))))

(define (expand-simple env exp cont)
  (expand-list env (cdr exp)
               (lambda (env expanded)
                 (cont env `(,(car exp) ,@expanded)))))

(define (expand-lambda env exp cont)
  (let ((internal-env (add-identifier-list env
                                  (cadr exp))))
    (expand-list internal-env (cadr exp)
                 (lambda (internal-env formals)
                   (expand-list internal-env (cddr exp)
                                (lambda (internal-env body)
                                  (cont env
                                        `(lambda ,formals
                                           ,@body))))))))

(define (expand-syntactic-closure free-names-syntactic-env exp cont)
  (expand (filter-syntactic-environment (syntactic-closure-free-names exp)
                                        free-names-syntactic-env
                                        (syntactic-closure-env exp))
          (syntactic-closure-exp exp)
          cont))

(define (expand-list env exps cont)
  (define (expand-list-aux env acc exps cont)
    (if (null? exps)
        (cont env (reverse acc))
        (expand env (car exps)
                (lambda (env expanded)
                  (expand-list-aux env (cons expanded acc) (cdr exps) cont)))))
  (expand-list-aux env '() exps cont))

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

(define (expanded-value env val)
  val)

(define define-syntax-expander
  (lambda (exp with-macro-env def-env)
    (let* ((keyword (cadr exp))
           (transformer (execute
                         (expand def-env (caddr exp) expanded-value)
                         core-interpretation-environment))
           (expander (make-expander #f ;; NOTE This will be adjusted shortly.
                                    transformer))
           (extended-env (extend-syntactic-environment
                          with-macro-env
                          keyword
                          expander)))
      (set-expander-env! expander extended-env)
      (make-syntactic-closure extended-env '() (when #f #f)))))

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
         (list (list 'define-syntax define-syntax-expander)
               (list 'delay delay-expander)
               (list 'or or-expander)
               (list 'and and-expander)
               (list 'let let-expander)
               (list 'cond cond-expander)
               (list 'case case-expander)
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
           (display `(list ,(+ 2 2) "wut"))
           (define-syntax let
             (sc-macro-transformer
              (lambda (exp def-env)
               `(begin
                  (display "letting ")
                  (display ',(cadr exp))
                  (display " to do ")
                  (display ',(caddr exp))
                  (newline)))))
           (lambda (let)
             (let ((a b))
               c))
           (lambda (let*)
             (let ((a b))
               c))
           (define-syntax foo
             (sc-macro-transformer
              (lambda (exp def-env)
                `(+ ,(cadr exp)
                    ,(caddr exp)))))
           (foo 5 23))
        expanded-value)
