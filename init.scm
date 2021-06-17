;; The init file for the macro system.
  ;; Some of these macros were taken from the great Chibi Scheme implementation.
  ;; Copyright (c) 2009-2012 Alex Shinn.  All rights reserved.
  ;; BSD-style license: http://synthcode.com/license.txt

(begin
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

  ;; TODO Add more macros!
  )
