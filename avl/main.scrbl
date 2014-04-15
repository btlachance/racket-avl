#lang scribble/manual

@require[scribble/eval]

@require[(for-label racket)
         (for-label "main.rkt")]

@define[avl-eval (make-base-eval)]
@interaction-eval[#:eval avl-eval (require "main.rkt")]

@title{AVL Trees}
@author+email["Jan Dvořák" "mordae@anilinux.org"]

@defmodule[avl]

A self-balancing binary search tree variant.

All mutations of the AVL tree create new nodes instead of modifying the
data in place.  The imperative variants change the root node in place
for convenience.

These trees be used for as priority queues with possibility to remove
elements from the middle.

@section{Creating Trees}

@defproc[(make-avl (<=? (-> any/c any/c boolean?))) avl?]{
  Create new tree using specified comparator function.

  Tree with @racket[number?] elements would use @racket[<=] as the comparator,
  trees with @racket[string?] elements would use @racket[string<=?] and so on.

  @examples[#:eval avl-eval
    (define tree (make-avl <=))
    (avl-insert! tree 42)
  ]
}

@defproc[(avl-copy (tree avl?)) avl?]{
  Copy the tree container, effectively creating a standalone copy of tree
  decoupled from the original.

  @examples[#:eval avl-eval
    (define copy (avl-copy tree))
    (avl-remove! copy 42)
  ]
}


@section{Predicates}

@defproc[(avl? (v any/c)) boolean?]{
  Predicate identifying the AVL tree.

  @examples[#:eval avl-eval
    (avl? tree)
    (avl? copy)
    (avl? 'something-else)
  ]
}

@defproc[(avl-empty? (tree avl?)) boolean?]{
  Determine whether the tree contains no values.

  @examples[#:eval avl-eval
    (avl-empty? tree)
    (avl-empty? copy)
  ]
}

@defproc[(avl-contains? (tree avl?) (value any/c)) boolean?]{
  Determine whether the tree contains specified value at least once.

  @examples[#:eval avl-eval
    (avl-contains? tree 42)
    (avl-contains? copy 42)
  ]
}


@section{Manipulating Values}

@defproc[(avl-insert (tree avl?) (value any/c)) avl?]{
  Create new tree containing specified @racket[value].
  Values can be added to the tree multiple times.

  @examples[#:eval avl-eval
    (let ((new-tree (avl-insert tree 13)))
      (avl-contains? new-tree 13))
    (avl-contains? tree 13)
  ]
}

@defproc[(avl-insert! (tree avl?) (value any/c)) void?]{
  Like @racket[avl-insert], but the container is modified in place.

  @examples[#:eval avl-eval
    (avl-insert! tree 13)
    (avl-contains? tree 13)
  ]
}

@defproc[(avl-remove (tree avl?) (value any/c)) avl?]{
  Create new tree without the first instance of the @racket[value].
  If the tree contains the @racket[value] multiple times, other
  instances are left alone.

  @examples[#:eval avl-eval
    (let ((new-tree (avl-remove tree 13)))
      (avl-contains? new-tree 13))
    (avl-contains? tree 13)
  ]
}

@defproc[(avl-remove! (tree avl?) (value any/c)) void?]{
  Like @racket[avl-remove], but the container is modified in place.

  @examples[#:eval avl-eval
    (avl-remove! tree 13)
    (avl-contains? tree 13)
  ]
}


@section{Queue Usage}

@defproc[(avl-min (tree avl?)) any/c]{
  Find smallest (leftmost) value in the tree.

  @examples[#:eval avl-eval
    (avl-insert! tree 21)
    (avl-min tree)
  ]
}

@defproc[(avl-max (tree avl?)) any/c]{
  Find largest (rightmost) value in the tree.

  @examples[#:eval avl-eval
    (avl-insert! tree 101)
    (avl-max tree)
  ]
}

@defproc[(avl-pop-min (tree avl?)) (values any/c avl?)]{
  Find and remove smallest (leftmost) value from the tree.
  Returns both the removed value and new tree container.

  @examples[#:eval avl-eval
    (avl-pop-min tree)
    (avl-min tree)
  ]
}

@defproc[(avl-pop-min! (tree avl?)) any/c]{
  Like @racket[avl-pop-min], but returns only the value and
  modifies the container in place.

  @examples[#:eval avl-eval
    (avl-pop-min! tree)
    (avl-min tree)
  ]
}

@defproc[(avl-pop-max (tree avl?)) (values any/c avl?)]{
  Find and remove largest (rightmost) value from the tree.
  Returns both the removed value and new tree container.

  @examples[#:eval avl-eval
    (avl-pop-max tree)
    (avl-max tree)
  ]
}

@defproc[(avl-pop-max! (tree avl?)) any/c]{
  Like @racket[avl-pop-max], but returns only the value and
  modifies the container in place.

  @examples[#:eval avl-eval
    (avl-pop-max! tree)
    (avl-max tree)
  ]
}


@section{Iterating Over Values}

@defproc[(in-avl (tree avl?)) sequence?]{
  Iterate over the tree values in ascending order.

  @examples[#:eval avl-eval
    (for/list ((value (in-avl tree)))
      (* value 10))
  ]
}

@defproc[(in-avl/reverse (tree avl?)) sequence?]{
  Iterate over the tree values in descending order.

  @examples[#:eval avl-eval
    (for/list ((value (in-avl/reverse tree)))
      (/ value 10))
  ]
}

@defproc[(avl->list (tree avl?)) list?]{
  Convert the tree to an ordered list.

  @examples[#:eval avl-eval
    (avl->list tree)
    (avl->list copy)
  ]
}


@; vim:set ft=scribble sw=2 ts=2 et: