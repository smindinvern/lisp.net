(defun car (xs)
  (let (((head . tail) xs))
    head
    )
  )
(defun cdr (xs)
  (let (((head . tail) xs))
    tail
    )
  )
(defun fib (m n l i)
  (if (= i 0)
      l
    (fib n (+ m n) (n . l) (- i 1))
    )
  )

; Test recursion.
(defun test1 ()
  (let ((fibs (fib 1 1 '() 20))
	(correct '(10946 6765 4181 2584 1597 987 610 377 233 144 89 55 34 21 13 8 5 3 2 1)))
    (= ((car fibs) . (cdr fibs)) correct)
    )
  )

; Test pattern matching and recursion.
(defun rev-tail (xs rest)
  (case xs
	(
	 (
	  (x1 x2)
	  (x2 . (x1 . rest))
	  )
	 (
	  (head . tail)
	  (rev-tail tail (head . rest))
	  )
	 )
	)
  )
(defun rev (xs) (rev-tail xs '()))
(defun test2 ()
  (let ((list '(1 2 3 4 5 6 7 8 9))
	(correct '(9 8 7 6 5 4 3 2 1)))
    (= (rev list) correct)
    )
  )

(defun sumClosure (x y)
  (lambda ()
    (+ x y)
    )
  )

; Test that lambdas capture values.
(defun test3 ()
  (let (
	(closure1 (sumClosure 2 2))
	(closure2 (sumClosure 4 4))
	)
    (= (+ (closure1) (closure2)) 12)
    )
  )

; Test map function.
(defun test4 ()
  (let ((f (lambda (x) (+ x 1))))
    (= (map f '(1 2 3 4 5)) '(2 3 4 5 6))
    )
  )

(define-syntax macro
  (syntax-rules ()
                ((macro x f)
                 (let ((y 4))
                   (f (+ y x))
		   )
		 )
		)
  )
; Test that macros are hygienic.
(defun test5 ()
  (let ((x 12)
	(y 2))
    (let ((f (lambda (y) (+ x y))))
      (= (macro y f) 18)
      )
    )
  )
;; TODO: Naming the following as `macro' redefines the above `macro' and
;; causes this code to be invoked in `test5' above.
(define-syntax macro2
  (syntax-rules ()
		((macro2 (((z ...) ...) ((x ...) y) ...))
		 '((x y z ...) ... ...)
		 )
		)
  )
(defun test6 ()
  (let ((m (macro2 (((g h) (i j)) ((a b) c) ((d e) f))))
	(correct '((a c g h) (b f i j) (d c g h) (e f i j))))
    (= m correct)
    )
  )

(define-syntax macro3
  (syntax-rules ()
                ((macro3 ((a b ...) ...))
                 '((a b) ... ...)
		 )
		)
  )
(defun test7 ()
  (let ((m (macro3 ((a b c) (d e f))))
	(correct '((a b) (d c) (a e) (d f))))
    (= m correct)
    )
  )

(define-syntax macro4
  (syntax-rules ()
                ((macro4 ((a b ...) ...))
                 '((a ... b) ... ...)
		 )
		)
  )
(defun test8 ()
  (let ((m (macro4 ((a b c) (d e f) (g h i) (j k l))))
	(correct '((a d g j b) (a d g j c) (a d g j e) (a d g j f) (a d g j h) (a d g j i) (a d g j k) (a d g j l))))
    (= m correct)
    )
  )

(define-syntax macro5
  (syntax-rules ()
                ((macro5 (((z ...) ...) ((x ...) y) ...))
                 '((x y z) ... ...)
		 )
		)
  )
(defun test9 ()
  (let ((m (macro5 (((g h) (i j)) ((a b) c) ((d e) f))))
	(correct '((a c g) (b f h) (d c i) (e f j))))
    (= m correct)
    )
  )

(define-syntax macro6
  (syntax-rules ()
                ((macro6 ((a b ...) ...))
                 '((a ... a b) ... ...)
		 )
		)
  )
(defun test10 ()
  (let ((m (macro6 ((a b c) (d e f))))
	(correct '((a d a b) (a d d c) (a d a e) (a d d f))))
    (= m correct)
    )
  )

(define-syntax macro7
  (syntax-rules ()
                ((macro7 ((a b c ...) ...))
		 '((let ((a b)) c ...) ...)
		 )
		)
  )
(defun test11 ()
  (let ((m (macro7 ((a b c d) (d c b a))))
	(correct '((let ((a b)) c d) (let ((d c)) b a))))
    (= m correct)
    )
  )

(defun f (x y)
  (let ((g (lambda (z)
	     (f (- x 1) z)
	     )
	   )
	)
    (if (= x 0)
	y
      (g (+ y 1))
      )
    )
  )
(defun test12 ()
  (= (f 2 4) 6)
  )

(defun forall (f xs)
  (case xs
	(
	 ((x . ()) (f x))
	 (_ (if (f (car xs)) (forall f (cdr xs))))
	 )
	)
  )

(defun apply (f) (f))

(defun main ()
  (forall apply '(test1 test2 test3 test4 test5 test6 test7 test8 test9 test10 test11 test12))
  )

