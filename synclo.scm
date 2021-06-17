;; Gensym:

(define *gensym-counter* 0)
(define (gensym root)
  (set! *gensym-counter* (+ 1 *gensym-counter*))
  (string->symbol
   (string-append (symbol->string root)
                  (number->string *gensym-counter*))))

;; Syntactic closures:

(define-struct syntactic-closure (env free-names exp))

(define (make-syntactic-closure-list env free-names exps)
  (map (lambda (exp)
         (make-syntactic-closure env free-names exp))
       exps))

;; Environments:

(define (extend-environment outer-env keyword expander)
  (cons (cons keyword expander)
        outer-env))

(define (add-identifier outer-env identifier)
  (let ((variable (gensym identifier)))
    (extend-environment outer-env identifier variable)))

(define (add-identifier-list env identifiers)
  (if (null? identifiers)
      env
      (add-identifier (add-identifier-list env
                                           (cdr identifiers))
                      (car identifiers))))

(define (filter-environment names names-syntactic-env else-syntactic-env)
  (append (filter (lambda (expander)
                    (memq (car expander) names))
                  names-syntactic-env)
          else-syntactic-env))

(define (environment-def env keyword)
  (assoc keyword env))

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
  (let ((def (environment-def env exp)))
    (if def
        (if (expander? (cdr def))
            ;; FIXME Could this allow for symbol expansion?
            (expand-free-variable env exp cont)
            (cont env (cdr def)))
        (expand-free-variable env exp cont))))

(define (expand-application env exp cont)
  (let* ((op (car exp))
         (def (if (syntactic-closure? op)
                  (environment-def (syntactic-closure-env op)
                                   (syntactic-closure-exp op))
                  (environment-def env op))))
    (if def
        (if (expander? (cdr def))
            (expand-expander (cdr def) env exp cont)
            ;; NOTE Originally the cdr is expanded in the outer env.
            (expand-combination env exp cont))
        (expand-combination env exp cont))))

(define (expand-expander expander env exp cont)
  ;; NOTE The original paper implementation requires the expanded value to be a syntactic closure.
  ((expander-proc expander)
   exp
   env
   (expander-env expander)
   (lambda (env expanded)
     (expand env expanded cont))))

(define (expand-combination env exp cont)
  (expand-list env exp
               (lambda (env expanded)
                 (cont env `(,@expanded)))))

(define (expand-simple env exp cont)
  (expand-list env (cdr exp)
               (lambda (env expanded)
                 (cont env `(,(car exp) ,@expanded)))))

(define (expand-lambda env exp cont)
  (expand-list (add-identifier-list env
                                    ;; FIXME This means that nested macros that introduce new renames will have collisions.
                                    (filter (lambda (f)
                                              (not (syntactic-closure? f)))
                                            (cadr exp)))
               (cadr exp)
               (lambda (internal-env formals)
                 (expand-list internal-env (cddr exp)
                              (lambda (internal-env body)
                                (cont env
                                      `(lambda ,formals
                                         ,@body)))))))

(define (expand-syntactic-closure use-env exp cont)
  (expand (filter-environment (syntactic-closure-free-names exp)
                              use-env
                              (syntactic-closure-env exp))
          (syntactic-closure-exp exp)
          (lambda (env expanded)
            (cont use-env
                  expanded))))

(define (expand-list env exps cont)
  (define (expand-list-aux env-acc acc exps cont)
    (if (null? exps)
        (cont env-acc (reverse acc))
        (expand env-acc (car exps)
                (lambda (env-acc expanded)
                  (expand-list-aux env-acc (cons expanded acc) (cdr exps) cont)))))
  (expand-list-aux env '() exps cont))

;; Interpreter:

(define (execute env exp cont)
  ((cond ((syntactic-closure? exp) execute-syntactic-closure)
         ((symbol? exp) execute-symbol)
         ((not (pair? exp)) execute-constant)
         (else (case (car exp)
                 ((quote) execute-quote)
                 ((if) execute-if)
                 ((begin) execute-begin)
                 ((set!) execute-set!)
                 ((define) execute-define)
                 ((lambda) execute-lambda)
                 (else execute-application))))
   env
   exp
   cont))

(define (execute-syntactic-closure env exp cont)
  (execute env
           (syntactic-closure-exp exp)
           (lambda (env exp)
             (make-syntactic-closure (syntactic-closure-env exp)
                                     (syntactic-closure-free-names exp)
                                     expr))))

(define (execute-symbol env exp cont)
  (let ((def (environment-def env exp)))
    (cond ((not def)
           (error "Undefined variable" exp))
          ((expander? (cdr def))
           (error "Attempting to use an expander outside of static scope" exp))
          ;; NOTE These are introduced by define & lambdas.
          ((box? (cdr def))
           (cont env (unbox (cdr def))))
          (else
           (cont env (cdr def))))))

(define (execute-constant env exp cont)
  (cont env exp))

(define (execute-quote env exp cont)
  (cont env (cadr exp)))

(define (execute-if env exp cont)
  (execute env (cadr exp)
           (lambda (_ condition)
             (execute env
                      (cond (condition
                             (caddr exp))
                            ((= (length exp) 4)
                             (cadddr exp))
                            (else
                             (when #f #f)))
                      cont))))

(define (execute-begin env exp cont)
  (execute-list env (cdr exp) cont))

(define (execute-list env exps cont)
  (define (execute-list-aux env-acc acc exps cont)
    (if (null? exps)
        (cont env-acc acc)
        (execute env-acc (car exps)
                 (lambda (env-acc value)
                   (execute-list-aux env-acc value (cdr exps) cont)))))
  (execute-list-aux env (when #f #f) exps cont))

(define (execute-set! env exp cont)
  (let ((def (environment-def env (cadr exp))))
    (if def
        (execute env (caddr exp)
                 (lambda (env value)
                   (set-box! (cdr def) value)
                   (cont env value)))
        (error "Undefined variable" (cadr exp)))))

(define (execute-define env exp cont)
  (let* ((name (cadr exp))
         (value (caddr exp))
         (extended-env (extend-environment env name (box #f))))
    (execute extended-env value
             (lambda (_ executed)
               (set-box! (cdr (environment-def extended-env name))
                         executed)
               (cont extended-env
                     (when #f #f))))))

(define (execute-lambda env exp cont)
  (let ((formals (cadr exp))
        (body (cddr exp)))
    (cont env
          (lambda args
            (if (equal? (length args)
                        (length formals))
                (let ((extended-env (foldl (lambda (binding env)
                                             (extend-environment env
                                                                 (car binding)
                                                                 (box (cdr binding))))
                                           env
                                           (map cons
                                                formals
                                                args))))
                  (execute-list extended-env
                                body
                                resulting-value))
                (error "Arity mismatch" (length args)))))))

(define (execute-application env exp cont)
  (define (execute-args env-acc acc args cont)
    (if (null? args)
        (cont env-acc (reverse acc))
        (execute env (car args)
                 (lambda (env-acc arg)
                   (execute-args env-acc (cons arg acc) (cdr args) cont)))))
  (execute env (car exp)
           (lambda (_ op)
             (execute-args env '() (cdr exp)
                           (lambda (_ args)
                             (cont env (apply op args)))))))

;; Interpretation env:

(define (resulting-value env val)
  val)

(define (identifier? id)
  (or (symbol? id)
      (and (syntactic-closure? id)
           (symbol? (syntactic-closure-exp id)))))

(define (identifier=? env1 id1 env2 id2)
  (and (identifier? id1)
       (identifier? id2)
       (equal? (expand env1 id1 resulting-value)
               (expand env2 id2 resulting-value))))

(define (every pred list)
  (if (null? list)
      #t
      (and (pred (car list))
           (every pred (cdr list)))))

(define (some pred list)
  (if (null? list)
      #f
      (or (pred (car list))
          (some pred (cdr list)))))

(define (find pred list)
  (cond ((null? list)
         #f)
        ((pred (car list))
         (car list))
        (else
         (find pred (cdr list)))))

(define (cons-source kar kdr source)
  (cons kar kdr))

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
                   (set! renames (cons (cons identifier name)
                                       renames))
                   name))))
         (lambda (x y)
           (identifier=? use-env x use-env y))))))

(define core-interpretation-environment
  (list (cons 'not not)
        (cons 'null? null?)
        (cons 'pair? pair?)
        (cons 'list? list?)
        (cons 'cons cons)
        (cons 'car car)
        (cons 'cdr cdr)
        (cons 'list list)
        (cons 'length length)
        (cons 'append append)
        (cons 'caar caar)
        (cons 'cdar cdar)
        (cons 'cadr cadr)
        (cons 'caddr caddr)
        (cons 'cddr cddr)
        (cons 'cdddr cdddr)
        (cons 'eqv? eqv?)
        (cons 'eq? eq?)
        (cons 'equal? equal?)
        (cons 'memv memv)
        (cons 'memq memq)
        (cons 'member member)
        (cons 'assv assv)
        (cons 'assq assq)
        (cons 'assoc assoc)
        (cons 'every every)
        (cons 'some some)
        (cons 'find find)
        (cons 'map map)
        (cons 'filter filter)
        (cons 'foldl foldl)
        (cons 'vector vector)
        (cons 'vector? vector?)
        (cons 'list->vector list->vector)
        (cons 'vector->list vector->list)
        (cons 'string->symbol string->symbol)
        (cons 'symbol->string symbol->string)
        (cons 'string-append string-append)
        (cons 'number->string number->string)
        (cons '+ +)
        (cons '- -)
        (cons '* *)
        (cons '/ /)
        (cons '= =)
        (cons '< <)
        (cons '> >)
        (cons '<= <=)
        (cons '>= >=)
        (cons 'cons-source cons-source)
        (cons 'error error)
        (cons 'make-syntactic-closure make-syntactic-closure)
        (cons 'identifier? identifier?)
        (cons 'identifier=? identifier=?)
        (cons 'sc-macro-transformer sc-macro-transformer)
        (cons 'rsc-macro-transformer rsc-macro-transformer)
        (cons 'er-macro-transformer er-macro-transformer)))

;; Expanders:

(define-struct expander ((env #:mutable) proc))

(define define-syntax-expander
  (lambda (exp define-syntax-env def-env cont)
    (let* ((keyword (cadr exp))
           (transformer (execute core-interpretation-environment
                                 (expand define-syntax-env
                                         (caddr exp)
                                         resulting-value)
                                 resulting-value))
           (expander (make-expander #f ;; NOTE This will be adjusted shortly.
                                    (lambda (exp use-env def-env cont)
                                      ;; NOTE Use-defined macros canot introduce new definitions,
                                      ;; NOTE unless they expand into a `define-syntax` call.
                                      (cont use-env
                                            (transformer exp use-env def-env)))))
           (extended-env (extend-environment
                          define-syntax-env
                          keyword
                          expander)))
      (set-expander-env! expander extended-env)
      ;; NOTE Continues expansion with the env extended with by the new macro definition.
      (cont extended-env
            (when #f #f)))))

;; Global syntactic env:

(define scheme-environment
  (list (cons 'define-syntax
              (make-expander '()
                             define-syntax-expander))))

;; Example:

(let ((code (with-input-from-file
                "tests.scm"
              (lambda ()
                (read)))))
  (expand scheme-environment
          (with-input-from-file
              "init.scm"
            (lambda ()
              (read)))
          (lambda (env _)
            (expand env
                    code
                    (lambda (_ expanded)
                      (displayln ";; Input code:")
                      (pretty-print code)
                      (newline)
                      (displayln ";; Expanded code:")
                      (pretty-print expanded))))))
