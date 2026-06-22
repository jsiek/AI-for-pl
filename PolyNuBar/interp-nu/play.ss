(load "reduce.ss")
(load "test.ss")

(define id-x
  `(lambda (x : X) x))

(define id-X
  `(Lambda (X) ,id-x (-> X X)))

(define id-type
  `(forall (X) (-> X X)))

;;`(cast id-X (,id-type => p (-> ,id-type ,id-type)))

(test 
 'simple-jack
 `((inst ((cast (inst ,id-X dyn) ((-> dyn dyn) => p (-> ,id-type ,id-type)))
          ,id-X)
         int)
   42)
 42)

(test 
 'simple-non-jack
 `((inst ((cast (inst ,id-X ,id-type) 
                ((-> ,id-type ,id-type) => p (-> ,id-type ,id-type)))
          ,id-X)
         int)
   42)
 42)
