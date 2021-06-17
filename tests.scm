;; Some tests for the macros.
(begin
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

  (lambda (let)
    (let* ((a b))
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
       (define foo
         (lambda (a b)
           (+ a b)))
       `(+ ,(cadr exp)
           ,(caddr exp)
           ,(foo (cadr exp)
                 (caddr exp))))))

  (foo 5 23)

  (define-syntax bar
    (syntax-rules (+)
      ((bar a)
       a)
      ((bar a as ...)
       (+ a (bar as ...)))))

  (bar 1 2 3 4 5))
