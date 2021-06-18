;; Some tests for the macros.
(begin
  (let ((x 23))
    (* x 5))

  (or 1 2 3 4 5)

  (cond ((something? x)
         do this stuff)
        ((otherwise?)
         do some other stuff)
        (else
         do that))

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

  (display `(list ,(+ 2 2) ,@(1 2 3 4 5)))

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

  (define-syntax bar
    (syntax-rules (+)
      ((bar a)
       a)
      ((bar a as ...)
       (+ a (bar as ...)))))

  (bar 1 2 3 4 5)

  (define-for-syntax foo
    (lambda (a b)
      (+ a b)))

  (define-syntax baz
    (sc-macro-transformer
     (lambda (exp def-env)
       (list '+
             (cadr exp)
             (caddr exp)
             (foo (cadr exp)
                  (caddr exp))))))
  (foo 5 23)
  (baz 5 23))
