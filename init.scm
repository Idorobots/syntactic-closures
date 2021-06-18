;; The init file for the macro system, these macros were taken from the great Chibi Scheme implementation.
;; Copyright (c) 2009-2012 Alex Shinn.  All rights reserved.
;; BSD-style license: http://synthcode.com/license.txt

(begin

  ;; Standard syntax transformers
  (define-for-syntax sc-macro-transformer
    (lambda (f)
      (lambda (expr use-env def-env)
        (make-syntactic-closure def-env '()
                                (f expr use-env)))))

  (define-for-syntax rsc-macro-transformer
    (lambda (f)
      (lambda (expr use-env def-env)
        (f expr def-env))))

  (define-for-syntax er-macro-transformer
    (lambda (f)
      (lambda (expr use-env def-env)
        ((lambda (renames)
           (f expr
              (lambda (identifier)
                ((lambda (renamed)
                   (if renamed
                       (cdr renamed)
                       ((lambda (name)
                          (set! renames (cons (cons identifier name)
                                              renames))
                          name)
                        (make-syntactic-closure def-env '() identifier))))
                 (assq identifier renames)))
              (lambda (x y)
                (identifier=? use-env x use-env y))))
         '()))))

  ;; Some macros to bootstrap the language.
  (define-syntax cond
    (er-macro-transformer
     (lambda (expr rename compare)
       (if (null? (cdr expr))
           (if #f #f)
           ((lambda (cl)
              (if (compare (rename 'else) (car cl))
                  (if (pair? (cddr expr))
                      (error "non-final else in cond" expr)
                      (cons (rename 'begin) (cdr cl)))
                  (if (if (null? (cdr cl)) #t (compare (rename '=>) (cadr cl)))
                      (list (list (rename 'lambda) (list (rename 'tmp))
                                  (list (rename 'if) (rename 'tmp)
                                        (if (null? (cdr cl))
                                            (rename 'tmp)
                                            (list (car (cddr cl)) (rename 'tmp)))
                                        (cons (rename 'cond) (cddr expr))))
                            (car cl))
                      (list (rename 'if)
                            (car cl)
                            (cons (rename 'begin) (cdr cl))
                            (cons (rename 'cond) (cddr expr))))))
            (cadr expr))))))

  (define-syntax and
    (er-macro-transformer
     (lambda (expr rename compare)
       (cond ((null? (cdr expr)))
             ((null? (cddr expr)) (cadr expr))
             (else (list (rename 'if) (cadr expr)
                         (cons (rename 'and) (cddr expr))
                         #f))))))

  (define-syntax quasiquote
    (er-macro-transformer
     (lambda (expr rename compare)
       (define qq
         (lambda (x d)
           (cond
            ((pair? x)
             (cond
              ((compare (rename 'unquote) (car x))
               (if (<= d 0)
                   (cadr x)
                   (list (rename 'list) (list (rename 'quote) 'unquote)
                         (qq (cadr x) (- d 1)))))
              ((compare (rename 'unquote-splicing) (car x))
               (if (<= d 0)
                   (list (rename 'cons) (qq (car x) d) (qq (cdr x) d))
                   (list (rename 'list) (list (rename 'quote) 'unquote-splicing)
                         (qq (cadr x) (- d 1)))))
              ((compare (rename 'quasiquote) (car x))
               (list (rename 'list) (list (rename 'quote) 'quasiquote)
                     (qq (cadr x) (+ d 1))))
              ((and (<= d 0) (pair? (car x))
                    (compare (rename 'unquote-splicing) (caar x)))
               (if (null? (cdr x))
                   (cadr (car x))
                   (list (rename 'append) (cadr (car x)) (qq (cdr x) d))))
              (else
               (list (rename 'cons) (qq (car x) d) (qq (cdr x) d)))))
            ((vector? x) (list (rename 'list->vector) (qq (vector->list x) d)))
            ((if (identifier? x) #t (null? x)) (list (rename 'quote) x))
            (else x))))
       (qq (cadr expr) 0))))

  (define-syntax case
    (er-macro-transformer
     (lambda (expr rename compare)
       (define body
         (lambda (exprs)
           (cond
            ((null? exprs)
             (rename 'tmp))
            ((compare (rename '=>) (car exprs))
             `(,(cadr exprs) ,(rename 'tmp)))
            (else
             `(,(rename 'begin) ,@exprs)))))
       (define clause
         (lambda (ls)
           (cond
            ((null? ls) #f)
            ((compare (rename 'else) (caar ls))
             (body (cdar ls)))
            ((and (pair? (car (car ls))) (null? (cdr (car (car ls)))))
             `(,(rename 'if) (,(rename 'eqv?) ,(rename 'tmp)
                              (,(rename 'quote) ,(car (caar ls))))
               ,(body (cdar ls))
               ,(clause (cdr ls))))
            (else
             `(,(rename 'if) (,(rename 'memv) ,(rename 'tmp)
                              (,(rename 'quote) ,(caar ls)))
               ,(body (cdar ls))
               ,(clause (cdr ls)))))))
       `(let ((,(rename 'tmp) ,(cadr expr)))
          ,(clause (cddr expr))))))

  (define-syntax letrec
    (er-macro-transformer
     (lambda (expr rename compare)
       ((lambda (defs)
          `((,(rename 'lambda) () ,@defs ,@(cddr expr))))
        (map (lambda (x) (cons (rename 'define) x)) (cadr expr))))))

  ;; Some utilities for let:
  (define-for-syntax every
    (lambda (pred list)
      (if (null? list)
          #t
          (and (pred (car list))
               (every pred (cdr list))))))

  (define-syntax let
    (er-macro-transformer
     (lambda (expr rename compare)
       (if (null? (cdr expr)) (error "empty let" expr))
       (if (null? (cddr expr)) (error "no let body" expr))
       ((lambda (bindings)
          (if (list? bindings)
              #f
              (error "bad let bindings"))
          (if (every (lambda (x)
                       (if (pair? x)
                           (if (pair? (cdr x))
                               (null? (cddr x))
                               #f)
                           #f))
                     bindings)
              ((lambda (vars vals)
                 (if (identifier? (cadr expr))
                     `((,(rename 'lambda) ,vars
                        (,(rename 'letrec) ((,(cadr expr)
                                             (,(rename 'lambda) ,vars
                                              ,@(cdr (cddr expr)))))
                         (,(cadr expr) ,@vars)))
                       ,@vals)
                     `((,(rename 'lambda) ,vars ,@(cddr expr)) ,@vals)))
               (map car bindings)
               (map cadr bindings))
              (error "bad let syntax" expr)))
        (if (identifier? (cadr expr)) (car (cddr expr)) (cadr expr))))))

  (define-syntax let*
    (er-macro-transformer
     (lambda (expr rename compare)
       (if (null? (cdr expr)) (error "empty let*" expr))
       (if (null? (cddr expr)) (error "no let* body" expr))
       (if (null? (cadr expr))
           `(,(rename 'let) () ,@(cddr expr))
           (if (if (list? (cadr expr))
                   (every
                    (lambda (x)
                      (if (pair? x) (if (pair? (cdr x)) (null? (cddr x)) #f) #f))
                    (cadr expr))
                   #f)
               `(,(rename 'let) (,(caar (cdr expr)))
                 (,(rename 'let*) ,(cdar (cdr expr)) ,@(cddr expr)))
               (error "bad let* syntax"))))))

  (define-syntax or
    (er-macro-transformer
     (lambda (expr rename compare)
       (cond ((null? (cdr expr)) #f)
             ((null? (cddr expr)) (cadr expr))
             (else
              (list (rename 'let) (list (list (rename 'tmp) (cadr expr)))
                    (list (rename 'if) (rename 'tmp)
                          (rename 'tmp)
                          (cons (rename 'or) (cddr expr)))))))))

  ;; Some utilities to make the syntax-rules macro kinda work.
  (define-for-syntax some
    (lambda (pred list)
      (if (null? list)
          #f
          (or (pred (car list))
              (some pred (cdr list))))))

  (define-for-syntax find
    (lambda (pred list)
      (cond ((null? list)
             #f)
            ((pred (car list))
             (car list))
            (else
             (find pred (cdr list))))))

  (define-for-syntax cons-source
    (lambda (kar kdr source)
      (cons kar kdr)))

  (define-for-syntax syntax-rules-transformer
    (lambda (expr rename compare)
      (let ((ellipsis-specified? (identifier? (cadr expr)))
            (count 0)
            (_er-macro-transformer (rename 'er-macro-transformer))
            (_lambda (rename 'lambda))      (_let (rename 'let))
            (_begin (rename 'begin))        (_if (rename 'if))
            (_and (rename 'and))            (_or (rename 'or))
            (_eq? (rename 'eq?))            (_equal? (rename 'equal?))
            (_car (rename 'car))            (_cdr (rename 'cdr))
            (_cons (rename 'cons))          (_pair? (rename 'pair?))
            (_null? (rename 'null?))        (_expr (rename 'expr))
            (_rename (rename 'rename))      (_compare (rename 'compare))
            (_quote (rename 'quote)) (_apply (rename 'apply))
            (_append (rename 'append))      (_map (rename 'map))
            (_vector? (rename 'vector?))    (_list? (rename 'list?))
            (_len (rename'len))             (_length (rename 'length*))
            (_- (rename '-))   (_>= (rename '>=))   (_error (rename 'error))
            (_ls (rename 'ls)) (_res (rename 'res)) (_i (rename 'i))
            (_reverse (rename 'reverse))
            (_vector->list (rename 'vector->list))
            (_list->vector (rename 'list->vector))
            (_cons3 (rename 'cons-source)))
        (define ellipsis (if ellipsis-specified? (cadr expr) (rename '...)))
        (define lits (if ellipsis-specified? (car (cddr expr)) (cadr expr)))
        (define forms (if ellipsis-specified? (cdr (cddr expr)) (cddr expr)))
        (define next-symbol
          (lambda (s)
            (set! count (+ count 1))
            (rename (string->symbol (string-append s (number->string count))))))
        (define ellipsis?
          (lambda (x)
            (and (pair? x) (pair? (cdr x)) (compare ellipsis (cadr x)))))
        (define ellipsis-escape?
          (lambda (x) (and (pair? x) (compare ellipsis (car x)))))
        (define ellipsis-depth
          (lambda (x)
            (if (ellipsis? x)
                (+ 1 (ellipsis-depth (cdr x)))
                0)))
        (define ellipsis-tail
          (lambda (x)
            (if (ellipsis? x)
                (ellipsis-tail (cdr x))
                (cdr x))))
        (define all-vars
          (lambda (x dim)
            (let lp ((x x) (dim dim) (vars '()))
              (cond ((identifier? x)
                     (if (some (lambda (lit) (compare x lit)) lits)
                         vars
                         (cons (cons x dim) vars)))
                    ((ellipsis? x) (lp (car x) (+ dim 1) (lp (cddr x) dim vars)))
                    ((pair? x) (lp (car x) dim (lp (cdr x) dim vars)))
                    ((vector? x) (lp (vector->list x) dim vars))
                    (else vars)))))
        (define free-vars
          (lambda (x vars dim)
            (let lp ((x x) (free '()))
              (cond
               ((identifier? x)
                (if (and (not (memq x free))
                         (cond ((assq x vars) => (lambda (cell) (>= (cdr cell) dim)))
                               (else #f)))
                    (cons x free)
                    free))
               ((pair? x) (lp (car x) (lp (cdr x) free)))
               ((vector? x) (lp (vector->list x) free))
               (else free)))))
        (define expand-template
          (lambda (tmpl vars)
            (let lp ((t tmpl) (dim 0))
              (cond
               ((identifier? t)
                (cond
                 ((find (lambda (v) (eq? t (car v))) vars)
                  => (lambda (cell)
                       (if (<= (cdr cell) dim)
                           t
                           (error "too few ...'s"))))
                 (else
                  (list _rename (list _quote t)))))
               ((pair? t)
                (cond
                 ((ellipsis-escape? t)
                  (list _quote
                        (if (pair? (cdr t))
                            (if (pair? (cddr t)) (cddr t) (cadr t))
                            (cdr t))))
                 ((ellipsis? t)
                  (let* ((depth (ellipsis-depth t))
                         (ell-dim (+ dim depth))
                         (ell-vars (free-vars (car t) vars ell-dim)))
                    (cond
                     ((null? ell-vars)
                      (error "too many ...'s"))
                     ((and (null? (cdr (cdr t))) (identifier? (car t)))
                      ;; shortcut for (var ...)
                      (lp (car t) ell-dim))
                     (else
                      (let* ((once (lp (car t) ell-dim))
                             (nest (if (and (null? (cdr ell-vars))
                                            (identifier? once)
                                            (eq? once (car vars)))
                                       once ;; shortcut
                                       (cons _map
                                             (cons (list _lambda ell-vars once)
                                                   ell-vars))))
                             (many (do ((d depth (- d 1))
                                        (many nest
                                              (list _apply _append many)))
                                       ((= d 1) many))))
                        (if (null? (ellipsis-tail t))
                            many ;; shortcut
                            (list _append many (lp (ellipsis-tail t) dim))))))))
                 (else (list _cons3 (lp (car t) dim) (lp (cdr t) dim) (list _quote t)))))
               ((vector? t) (list _list->vector (lp (vector->list t) dim)))
               ((null? t) (list _quote '()))
               (else t)))))
        (define expand-pattern
          (lambda (pat tmpl)
            (let lp ((p (cdr pat))
                     (x (list _cdr _expr))
                     (dim 0)
                     (vars '())
                     (k (lambda (vars)
                          (list _cons (expand-template tmpl vars) #f))))
              (let ((v (next-symbol "v.")))
                (list
                 _let (list (list v x))
                 (cond
                  ((identifier? p)
                   (if (some (lambda (l) (compare p l)) lits)
                       (list _and
                             (list _compare v (list _rename (list _quote p)))
                             (k vars))
                       (list _let (list (list p v)) (k (cons (cons p dim) vars)))))
                  ((ellipsis? p)
                   (cond
                    ((not (null? (cdr (cdr p))))
                     (cond
                      ((some (lambda (x) (and (identifier? x) (compare x ellipsis)))
                             (cddr p))
                       (error "multiple ellipses" p))
                      (else
                       (let ((len (length* (cdr (cdr p))))
                             (_lp (next-symbol "lp.")))
                         `(,_let ((,_len (,_length ,v)))
                                 (,_and (,_>= ,_len ,len)
                                        (,_let ,_lp ((,_ls ,v)
                                                     (,_i (,_- ,_len ,len))
                                                     (,_res (,_quote ())))
                                               (,_if (,_>= 0 ,_i)
                                                     ,(lp `(,(cddr p)
                                                            (,(car p) ,(car (cdr p))))
                                                          `(,_cons ,_ls
                                                                   (,_cons (,_reverse ,_res)
                                                                           (,_quote ())))
                                                          dim
                                                          vars
                                                          k)
                                                     (,_lp (,_cdr ,_ls)
                                                           (,_- ,_i 1)
                                                           (,_cons3 (,_car ,_ls)
                                                                    ,_res
                                                                    ,_ls))))))))))
                    ((identifier? (car p))
                     (list _and (list _list? v)
                           (list _let (list (list (car p) v))
                                 (k (cons (cons (car p) (+ 1 dim)) vars)))))
                    (else
                     (let* ((w (next-symbol "w."))
                            (_lp (next-symbol "lp."))
                            (new-vars (all-vars (car p) (+ dim 1)))
                            (ls-vars (map (lambda (x)
                                            (next-symbol
                                             (string-append
                                              (symbol->string
                                               (identifier->symbol (car x)))
                                              "-ls")))
                                          new-vars))
                            (once
                             (lp (car p) (list _car w) (+ dim 1) '()
                                 (lambda (_)
                                   (cons
                                    _lp
                                    (cons
                                     (list _cdr w)
                                     (map (lambda (x l)
                                            (list _cons (car x) l))
                                          new-vars
                                          ls-vars)))))))
                       (list
                        _let
                        _lp (cons (list w v)
                                  (map (lambda (x) (list x (list _quote '()))) ls-vars))
                        (list _if (list _null? w)
                              (list _let (map (lambda (x l)
                                                (list (car x) (list _reverse l)))
                                              new-vars
                                              ls-vars)
                                    (k (append new-vars vars)))
                              (list _and (list _pair? w) once)))))))
                  ((pair? p)
                   (list _and (list _pair? v)
                         (lp (car p)
                             (list _car v)
                             dim
                             vars
                             (lambda (vars)
                               (lp (cdr p) (list _cdr v) dim vars k)))))
                  ((vector? p)
                   (list _and
                         (list _vector? v)
                         (lp (vector->list p) (list _vector->list v) dim vars k)))
                  ((null? p) (list _and (list _null? v) (k vars)))
                  (else (list _and (list _equal? v p) (k vars)))))))))
        (list
         _er-macro-transformer
         (list _lambda (list _expr _rename _compare)
               (list
                _car
                (cons
                 _or
                 (append
                  (map
                   (lambda (clause) (expand-pattern (car clause) (cadr clause)))
                   forms)
                  (list
                   (list _cons
                         (list _error "no expansion for"
                               (list (rename 'strip-syntactic-closures) _expr))
                         #f))))))))))

  (define-syntax syntax-rules
    (er-macro-transformer
     (lambda (expr rename compare)
       (syntax-rules-transformer expr rename compare))))

  ;; TODO Add more macros!
  )
