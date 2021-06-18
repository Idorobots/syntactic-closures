;; Fresh-Symbol:

(define *fresh-symbol-counter* 0)

(define (rehashed-symbol root code)
  (string->symbol
   (format "~a~a" root code)))

(define (fresh-symbol root)
  (set! *fresh-symbol-counter* (+ 1 *fresh-symbol-counter*))
  (rehashed-symbol root *fresh-symbol-counter*))

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

(define (rename-identifier outer-env identifier)
  (let ((variable (fresh-symbol identifier)))
    (extend-environment outer-env identifier variable)))

(define (rename-identifier-list env identifiers)
  (if (null? identifiers)
      env
      (rename-identifier (rename-identifier-list env
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

(define (macro-expand env exp cont)
  ((cond ((syntactic-closure? exp) macro-expand-syntactic-closure)
         ((symbol? exp) macro-expand-symbol)
         ((not (pair? exp)) macro-expand-constant)
         (else (case (car exp)
                 ((quote) macro-expand-quote)
                 ((if begin set!) macro-expand-simple)
                 ((lambda) macro-expand-lambda)
                 (else macro-expand-application))))
   env
   exp
   cont))

(define (macro-expand-constant env exp cont)
  (cont env exp))

(define (macro-expand-quote env exp cont)
  (cont env
        (if (syntactic-closure? (cadr exp))
            `(quote ,(syntactic-closure-exp (cadr exp)))
            exp)))

(define (macro-expand-free-variable env exp cont)
  (cont env exp))

(define (identifier? id)
  (or (symbol? id)
      (and (syntactic-closure? id)
           (symbol? (syntactic-closure-exp id)))))

(define (macro-expand-symbol env exp cont)
  (let ((def (environment-def env exp)))
    (if def
        (if (identifier? (cdr def))
            (cont env (cdr def))
            ;; FIXME Could this allow for symbol expansion?
            (macro-expand-free-variable env exp cont))
        (macro-expand-free-variable env exp cont))))

(define (macro-expand-application env exp cont)
  (let* ((op (car exp))
         (def (if (syntactic-closure? op)
                  (environment-def (syntactic-closure-env op)
                                   (syntactic-closure-exp op))
                  (environment-def env op))))
    (if def
        (if (expander? (cdr def))
            (macro-expand-expander (cdr def) env exp cont)
            ;; NOTE Originally the cdr is expanded in the outer env.
            (macro-expand-combination env exp cont))
        (macro-expand-combination env exp cont))))

(define (macro-expand-expander expander env exp cont)
  ;; NOTE The original paper implementation requires the expanded value to be a syntactic closure.
  ((expander-proc expander)
   exp
   env
   (expander-env expander)
   (lambda (env expanded)
     (macro-expand env expanded cont))))

(define (macro-expand-combination env exp cont)
  (macro-expand-list env exp
                     (lambda (env expanded)
                       (cont env `(,@expanded)))))

(define (macro-expand-simple env exp cont)
  (macro-expand-list env (cdr exp)
                     (lambda (env expanded)
                       (cont env `(,(car exp) ,@expanded)))))

(define (macro-expand-lambda env exp cont)
  (macro-expand-list (rename-identifier-list env (cadr exp))
                     (cadr exp)
                     (lambda (internal-env formals)
                       (macro-expand-list internal-env (cddr exp)
                                          (lambda (internal-env body)
                                            (cont env
                                                  `(lambda ,formals
                                                     ,@body)))))))

(define (macro-expand-syntactic-closure use-env exp cont)
  (macro-expand (filter-environment (syntactic-closure-free-names exp)
                                    use-env
                                    (syntactic-closure-env exp))
                (syntactic-closure-exp exp)
                (lambda (_ expanded)
                  (cont use-env
                        expanded))))

(define (macro-expand-list env exps cont)
  (define (macro-expand-list-aux env-acc acc exps cont)
    (if (null? exps)
        (cont env-acc (reverse acc))
        (macro-expand env-acc (car exps)
                      (lambda (env-acc expanded)
                        (macro-expand-list-aux env-acc (cons expanded acc) (cdr exps) cont)))))
  (macro-expand-list-aux env '() exps cont))

;; Interpreter:

(define (evaluate env exp cont)
  ((cond ((syntactic-closure? exp) evaluate-syntactic-closure)
         ((symbol? exp) evaluate-symbol)
         ((not (pair? exp)) evaluate-constant)
         (else (case (car exp)
                 ((quote) evaluate-quote)
                 ((if) evaluate-if)
                 ((begin) evaluate-begin)
                 ((set!) evaluate-set!)
                 ((define) evaluate-define)
                 ((lambda) evaluate-lambda)
                 (else evaluate-application))))
   env
   exp
   cont))

(define (evaluate-syntactic-closure env exp cont)
  (evaluate env
            (syntactic-closure-exp exp)
            (lambda (env exp)
              (make-syntactic-closure (syntactic-closure-env exp)
                                      (syntactic-closure-free-names exp)
                                      expr))))

(define (evaluate-symbol env exp cont)
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

(define (evaluate-constant env exp cont)
  (cont env exp))

(define (evaluate-quote env exp cont)
  (cont env (cadr exp)))

(define (evaluate-if env exp cont)
  (evaluate env (cadr exp)
            (lambda (_ condition)
              (evaluate env
                        (cond (condition
                               (caddr exp))
                              ((= (length exp) 4)
                               (cadddr exp))
                              (else
                               (when #f #f)))
                        cont))))

(define (evaluate-begin env exp cont)
  (evaluate-list env (cdr exp) cont))

(define (evaluate-list env exps cont)
  (define (evaluate-list-aux env-acc acc exps cont)
    (if (null? exps)
        (cont env-acc acc)
        (evaluate env-acc (car exps)
                  (lambda (env-acc value)
                    (evaluate-list-aux env-acc value (cdr exps) cont)))))
  (evaluate-list-aux env (when #f #f) exps cont))

(define (evaluate-set! env exp cont)
  (let ((def (environment-def env (cadr exp))))
    (if def
        (evaluate env (caddr exp)
                  (lambda (env value)
                    (set-box! (cdr def) value)
                    (cont env value)))
        (error "Undefined variable" (cadr exp)))))

(define (evaluate-define env exp cont)
  (let* ((name (cadr exp))
         (value (caddr exp))
         (extended-env (extend-environment env name (box #f))))
    (evaluate extended-env value
              (lambda (_ executed)
                (set-box! (cdr (environment-def extended-env name))
                          executed)
                (cont extended-env
                      (when #f #f))))))

(define (evaluate-lambda env exp cont)
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
                  (evaluate-list extended-env
                                 body
                                 resulting-value))
                (error "Arity mismatch" (length args)))))))

(define (evaluate-application env exp cont)
  (define (evaluate-args env-acc acc args cont)
    (if (null? args)
        (cont env-acc (reverse acc))
        (evaluate env (car args)
                  (lambda (env-acc arg)
                    (evaluate-args env-acc (cons arg acc) (cdr args) cont)))))
  (evaluate env (car exp)
            (lambda (_ op)
              (evaluate-args env '() (cdr exp)
                             (lambda (_ args)
                               (cont env (apply op args)))))))

;; Interpretation env:

(define (resulting-value env val)
  val)

(define (identifier=? env1 id1 env2 id2)
  (and (identifier? id1)
       (identifier? id2)
       (equal? (macro-expand env1 id1 resulting-value)
               (macro-expand env2 id2 resulting-value))))

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
        (cons 'error error)
        (cons 'make-syntactic-closure make-syntactic-closure)
        (cons 'identifier? identifier?)
        (cons 'identifier=? identifier=?)
        (cons 'gensym fresh-symbol)))

;; Expanders:

(define-struct expander ((env #:mutable) proc))

(define define-syntax-expander
  (lambda (exp define-syntax-env def-env cont)
    (let* ((keyword (cadr exp))
           (transformer (evaluate define-syntax-env
                                  (macro-expand define-syntax-env
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

(define define-for-syntax-expander
  (lambda (exp define-env def-env cont)
    (let ((name (cadr exp))
          (value (caddr exp)))
      (macro-expand define-env
                    value
                    (lambda (env expanded)
                      ;; NOTE We put the evaluated function into the environment so that it's available for syntax...
                      (evaluate env
                                `(define ,name ,expanded)
                                (lambda (env _)
                                  (cont env
                                        ;; NOTE ...but also replace it with an interpretable variant.
                                        `(define ,name ,value)))))))))

;; Global syntactic env:

(define scheme-environment
  (list* (cons 'define-syntax
               (make-expander '()
                              define-syntax-expander))
         (cons 'define-for-syntax
               (make-expander '()
                              define-for-syntax-expander))
         core-interpretation-environment))

;; Examples:

(let ((code (with-input-from-file "tests.scm" (lambda () (read)))))
  (macro-expand scheme-environment
                (with-input-from-file "init.scm" (lambda () (read)))
                (lambda (env _)
                  (macro-expand env
                                code
                                (lambda (_ expanded)
                                  (displayln ";; Input code:")
                                  (pretty-print code)
                                  (newline)
                                  (displayln ";; Expanded code:")
                                  (pretty-print expanded))))))
