#lang typed/racket/base
;
; AVL - Binary Search Tree
;

(require racket/generator
         racket/bool
         racket/match)

(provide avl?)


;; Wrapper to hide AVL tree nodes from the user.
;; Possibly mutable, unlike the individual nodes.
(struct (a) avl
  ([<=? : (-> a a Boolean)] [=? : (-> a a Boolean)] [root : (U (node a) False)])
  #:mutable)

;; An immutable tree node.
(struct (a) node
  ([left : (U False (node a))] [right : (U False (node a))] [value : a] [height : Integer]))


;; Create an empty tree with specified comparator,
;; that determines two values are identical using equal?.
(: make-avl (All (a) (-> (-> a a Boolean) (avl a))))
(define (make-avl <=?)
  (avl <=? equal? #f))


;; Create an empty tree with specified comparator,
;; that determines two values are identical using eq?.
(: make-avleq (All (a) (-> (-> a a Boolean) (avl a))))
(define (make-avleq <=?)
  (avl <=? eq? #f))


;; Create an empty tree with specified comparator,
;; that determines two values are identical using eqv?.
(: make-avleqv (All (a) (-> (-> a a Boolean) (avl a))))
(define (make-avleqv <=?)
  (avl <=? eqv? #f))


;; Create an empty tree with specified comparator and equality predicate.
(: make-custom-avl (All (a) (-> (-> a a Boolean) (-> a a Boolean) (avl a))))
(define (make-custom-avl <=? =?)
  (avl <=? =? #f))


;; Determine whether the value is an AVL tree have been
;; created using `make-avl`.
(: avl-equal? (-> Any Boolean))
(define (avl-equal? v)
  (and (avl? v)
       (eq? equal? (avl-=? v))))


;; Determine whether the value is an AVL tree have been
;; created using `make-avleqv`.
(: avl-eqv? (-> Any Boolean))
(define (avl-eqv? v)
  (and (avl? v)
       (eq? eqv? (avl-=? v))))


;; Determine whether the value is an AVL tree have been
;; created using `make-avleq`.
(: avl-eq? (-> Any Boolean))
(define (avl-eq? v)
  (and (avl? v)
       (eq? eq? (avl-=? v))))


;; Determine whether is the AVL tree empty or not.
(: avl-empty? (All (a) (-> (avl a) Boolean)))
(define (avl-empty? tree)
  (not (avl-root tree)))


;; Create copy of the AVL tree.
;; Pretty cheap since nodes are immutable.
(: avl-copy (All (a) (-> (avl a) (avl a))))
(define (avl-copy tree)
  (match tree
    ((avl <=? =? root)
     (avl <=? =? root))))


;; Create new tree including given value.
(: avl-add (All (a) (-> (avl a) a (avl a))))
(define (avl-add tree value)
  (match tree
    ((avl <=? =? root)
     (avl <=? =? (add <=? =? root value)))))


;; Modify an existing tree to include given value.
(: avl-add! (All (a) (-> (avl a) a Void)))
(define (avl-add! tree value)
  (match tree
    ((avl <=? =? root)
     (set-avl-root! tree (add <=? =? root value)))))


;; Perform the non-modifying addition of a value into the tree.
(: add (All (a) (-> (-> a a Boolean) (-> a a Boolean) (U (node a) False) a (node a))))
(define (add <=? =? parent new-value)
  (match parent
    ((node left right value height)
     (cond
       ((=? value new-value)
        (make-node left right new-value))

       ((<=? new-value value)
        (rebalance
          (make-node (add <=? =? left new-value) right value)))

       (else
        (rebalance
          (make-node left (add <=? =? right new-value) value)))))

    (else
     (make-node #f #f new-value))))


;; Rebalance tree node if required.
(: rebalance (All (a) (-> (node a) (node a))))
(define (rebalance parent)
  (match parent
    ((node left right value _)
     (cond
       ((= (balance parent) 2)
        (if (and (= (balance left) -1) (not (false? left)))
            (let ((left (rotate-left left)))
              (rotate-right (make-node left right value)))
            (rotate-right parent)))

       ((= (balance parent) -2)
        (if (and (= (balance right) 1) (not (false? right)))
            (let ((right (rotate-right right)))
              (rotate-left (make-node left right value)))
            (rotate-left parent)))

       (else parent)))))


;; Create right-rotated version of the node.
(: rotate-right (All (a) (-> (node a) (node a))))
(define (rotate-right parent)
  (match parent
    ((node left right value _)
     (match left
       ;; Isn't an "else" missing here? What if left is #f? rotate-left seems
       ;; to have the same omission, but it's probably OK due to the balance
       ;; checks called in rebalance
       ((node l-left l-right l-value _)
        (let ((new-right (make-node l-right right value)))
          (make-node l-left new-right l-value)))))))


;; Create left-rotated version of the node.
(: rotate-left (All (a) (-> (node a) (node a))))
(define (rotate-left parent)
  (match parent
    ((node left right value _)
     (match right
       ((node r-left r-right r-value _)
        (let ((new-left (make-node left r-left value)))
          (make-node new-left r-right r-value)))))))


;; Create new node, automatically computing height using the
;; higher of left and right children.
(: make-node (All (a) (-> (Option (node a)) (Option (node a)) a (node a))))
(define (make-node left right value)
  (node left right value (add1 (max (height right) (height left)))))


;; Return height of node or 0 for #f.
(: height (All (a) (-> (U (node a) False) Integer)))
(define (height maybe-node)
  (if maybe-node (node-height maybe-node) 0))


;; Return balance for node or 0 for #f.
(: balance (All (a) (-> (U (node a) False) Integer)))
(define (balance maybe-node)
  (match maybe-node
    ((node left right _ _)
     (- (height left)
        (height right)))

    (else 0)))


;; Return minimal (leftmost) value in the tree.
(: avl-min (All (a) (-> (avl a) a)))
(define (avl-min tree)
  (match tree
    ((avl _ _ root)
     (when (false? root)
       (error 'avl-min "empty tree"))
     (leftmost root))))


;; Return maximal (rightmost) value in the tree.
(: avl-max (All (a) (-> (avl a) a)))
(define (avl-max tree)
  (match tree
    ((avl _ _ root)
     (when (false? root)
       (error 'avl-max "empty tree"))
     (rightmost root))))


;; Recursively reach leftmost value in the tree of nodes.
(: leftmost (All (a) (-> (node a) a)))
(define (leftmost parent)
  (match parent
    ((node left _ value _)
     (if (false? left)
         value
         (leftmost left)))))


;; Recursively reach rightmost value in the tree of nodes.
(: rightmost (All (a) (-> (node a) a)))
(define (rightmost parent)
  (match parent
    ((node _ right value _)
     (if (false? right)
         value
         (rightmost right)))))


;; Return tree's minimal item and a new tree without it.
(: avl-pop-min (All (a) (-> (avl a) (Values a (avl a)))))
(define (avl-pop-min tree)
  (match tree
    ((avl <=? =? root)
     (when (false? root)
       (error 'avl-pop-min "empty tree"))
     (let-values (((value new-root) (pop-min root)))
       (values value (avl <=? =? new-root))))))


;; Remove tree's minimal item and return it.
(: avl-pop-min! (All (a) (-> (avl a) a)))
(define (avl-pop-min! tree)
  (match tree
    ((avl _ _ root)
     (when (false? root)
       (error 'avl-pop-min! "empty tree"))
     (let-values (((value new-root) (pop-min root)))
       (set-avl-root! tree new-root)
       (begin value)))))


;; Recursively rebuild nodes without the leftmost node,
;; returning it's value and a new tree of nodes.
(: pop-min (All (a) (-> (node a) (Values a (node a)))))
(define (pop-min parent)
  (match parent
    ((node left right value _)
     (if (and (false? left) (not (false? right)))
         (values value right)
         (let-values (((result left) (pop-min left)))
           (values result (rebalance (make-node left right value))))))))


;; Return tree's maximal item and a new tree without it.
(: avl-pop-max (All (a) (-> (avl a) (Values a (avl a)))))
(define (avl-pop-max tree)
  (match tree
    ((avl <=? =? root)
     (when (false? root)
       (error 'avl-pop-max "empty tree"))
     (let-values (((value new-root) (pop-max root)))
       (values value (avl <=? =? new-root))))))


;; Remove tree's maximal item and return it.
(: avl-pop-max! (All (a) (-> (avl a) a)))
(define (avl-pop-max! tree)
  (match tree
    ((avl _ _ #f)
     (error 'avl-pop-max! "empty tree"))

    ((avl _ _ root)
     (let-values (((value new-root) (pop-max root)))
       (set-avl-root! tree new-root)
       (begin value)))))


;; Recursively rebuild nodes without the rightmost node,
;; returning it's value and a new tree of nodes.
(: pop-max (All (a) (-> (node a) (Values a (node a)))))
(define (pop-max parent)
  (match parent
    ((node left #f value _)
     (values value left))

    ((node left right value _)
     (let-values (((result right) (pop-max right)))
       (values result (rebalance (make-node left right value)))))))


;; Return new AVL tree without specified value.
(: avl-remove (All (a) (-> (avl a) a (avl a))))
(define (avl-remove tree value)
  (match tree
    ((avl <=? =? root)
     (with-handlers ((boolean? (λ _ tree)))
       (let ((new-root (remove-value <=? =? root value)))
         (avl <=? =? new-root))))))


;; Remove specified value from the AVL tree.
(: avl-remove! (All (a) (-> (avl a) a Void)))
(define (avl-remove! tree value)
  (match tree
    ((avl <=? =? root)
     (with-handlers ((boolean? void))
       (let ((new-root (remove-value <=? =? root value)))
         (set-avl-root! tree new-root))))))


;; Return node tree without specified target.
;; If the value is not present within the tree, raise #f.
(: remove-value (All (a) (-> (-> a a Boolean) (-> a a Boolean) (node a) a (node a))))
(define (remove-value <=? =? parent victim)
  (match parent
    ((node left right value _)
     (cond
       ((=? value victim)
        (cond
          ((and left right)
           (let-values (((value right) (pop-min right)))
             (rebalance (make-node left right value))))

          (else
           (or left right))))

       ((<=? victim value)
        (let ((left (remove-value <=? =? left victim)))
          (rebalance (make-node left right value))))

       (else
        (let ((right (remove-value <=? =? right victim)))
          (rebalance (make-node left right value))))))

    (else (raise #f))))


;; Determine whether the tree contains specified value.
(: avl-contains? (All (a) (-> (avl a) a Boolean)))
(define (avl-contains? tree value)
  (match tree
    ((avl <=? =? root)
     (contains? <=? =? root value))))


;; Return value corresponding to specified needle.
(: contains? (All (a) (-> (-> a a Boolean) (-> a a Boolean) (node a) a Boolean)))
(define (contains? <=? =? parent needle)
  (match parent
    ((node left right value _)
     (cond
       ((=? value needle)
        (begin #t))

       ((<=? needle value)
        (contains? <=? =? left needle))

       (else
        (contains? <=? =? right needle))))

    (else #f)))


;; Create ordered value sequence.
(: in-avl (All (a) (-> (avl a) (Sequenceof a))))
(define (in-avl tree)
  (in-generator
    (let iterate ((parent (avl-root tree)))
      (match parent
        ((node left right value _)
         (iterate left)
         (yield value)
         (iterate right))

        (else #t)))))


;; Create reverse ordered value sequence.
(: in-avl/reverse (All (a) (-> (avl a) (Sequenceof a))))
(define (in-avl/reverse tree)
  (in-generator
    (let iterate ((parent (avl-root tree)))
      (match parent
        ((node left right value _)
         (iterate right)
         (yield value)
         (iterate left))

        (else #t)))))


;; Convert the tree to a list.
(: avl->list (All (a) (-> (avl a) (Listof a))))
(define (avl->list tree)
  (for/list ((x (in-avl tree))) x))


; vim:set ts=2 sw=2 et:
