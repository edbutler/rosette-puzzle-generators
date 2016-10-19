; A little Sudoku generator to illustrate solving 2QBF problems with Rosette.
; This is not meant to be an efficient or high quality Sudoku generator;
; it's intended to illustrate how to use Rosette.
;
; The Rosette library can be found at http://emina.github.io/rosette/
;
; author: Eric D Butler (edbutler@cs.washignton.edu)
; date: 2016 October 19
; license: MIT

#lang rosette

(current-bitwidth #f) ; required for forall, but we aren't using numbers anyway

(require
  rosette/lib/angelic) ; required for choose*

; Define the board size. We currently only support square boards.
; this code assumes the board size constant; some code is not rosette-safe otherwise.
; you can make this higher, but it gets a lot slower pretty quickly!
; I've only tried up to 9x9 boards (box-size = 3)
(define box-size 2)
(define row-size (* box-size box-size))
(define board-size (* row-size row-size))

; prints out a puzzle to the console
(define (print-puzzle cells)
  (for ([r row-size])
    (for ([c row-size])
      (define v (cell-ref cells r c))
      (printf "~a" (or v " ")))
    (printf "\n")))

; We use symbols instead of numbers for the cell entires for performance. But anything would work.
; (listof symbol?)
(define possible-entries
  (for/list ([i row-size])
    (string->symbol (format "~a" (add1 i)))))

; Creates a symbolic cell by choosing one of the possible entries.
; Takes in an ignored argument so it works well with build-list and friends.
; any/c -> symbol?
(define (symbolic-cell _)
  (apply choose* possible-entries))

; For accessing rows/columns/boxes of a board:
; We just use array index arithmetic. Since the board size is concrete,
; this is all concrete computation, and therefore has no impact on the
; performance of the solver, so we can do the easy thing.

; (listof 'a), integer?, integer? -> 'a
; Get the cell from the board represented by lst at row and col.
(define (cell-ref lst row col)
  (list-ref lst (+ (* row-size col) row)))

; Get an entire row of the board
; (listof 'a), integer? -> (listof 'a)
(define (get-row cells r)
  (build-list row-size (λ (c) (cell-ref cells r c))))

; Get an entire column of the board
; (listof 'a), integer? -> (listof 'a)
(define (get-col cells c)
  (build-list row-size (λ (r) (cell-ref cells r c))))

; Get an entire box (those typically 3x3 regions of sudoku boards).
; (listof 'a), integer? -> (listof 'a)
(define (get-box cells b)
  (define all-boxes
    (for*/list ([r box-size]
                [c box-size])
      (cons r c)))
  (match-define (cons br bc) (list-ref all-boxes b))
  (build-list row-size
    (λ (i)
      (match-define (cons ir ic) (list-ref all-boxes i))
      (cell-ref
        cells
        (+ (* box-size br) ir)
        (+ (* box-size bc) ic)))))

; Whether the given board (as a list of symbols) is solved.
; (listof symbol?) -> boolean?
(define (board-solved? cells)
  ; grabbing all the blocks is a concrete calculation even if the cells
  ; in the list are symbolic because the list itself is concrete.
  ; so we can be lazy and use rosette-unsafe functions.
  (define all-blocks
    (append
      (build-list row-size (curry get-row cells))
      (build-list row-size (curry get-col cells))
      (build-list row-size (curry get-box cells))))
  ; this computation
  (apply &&
    (map (λ (b) (apply distinct? b)) all-blocks)))

; Create a symbolic boolean. Just a shorthand to create symbolic values in expression-form
; -> boolean?
(define (!!)
  (define-symbolic* b boolean?)
  b)

; (listof (or/c symbol? false?)) -> (or/c (listof symbol?) #f)
(define (solve-puzzle puzzle)
  ; create symbolic cells only for ones that are #f, leave the rest
  (define cells (map (λ (c) (or c (symbolic-cell 0))) puzzle))
  (define soln
    (solve
      (assert (board-solved? cells))))
  (and (sat? soln) (evaluate cells soln)))

; Generates a valid (unique solution) sudoku puzzle.
; -> (listof (or/c symbol? false?))
(define (generate-puzzle)
  ; The primary solution.
  ; Here it's entirely symbolic, but we could make particular cells (or the entire thing!)
  ; concrete to control the puzzle we are creating.
  (define cells (build-list board-size symbolic-cell))
  ; hints are whether or not we provide the corresponding cell of the primary solution
  (define hints (build-list board-size (λ (_) (!!))))
  ; with-asserts not actually needed for choose*, but if we were to use something with implicit asserts
  ; for symcell this would be necessary, so leaving it in the example.
  (define-values (alt-cells alt-asserts) (with-asserts (build-list board-size symbolic-cell)))

  ; an arbitrary design constraint. Try your own here!
  (define max-desired-hints
    (match box-size
     [2 4] ; 4 is minimal for 4x4 boards
     [3 40])) ; this is not minimal for 9x9 but it takes longer with lower vlaues.

  (define soln (time
    (solve
      (begin
        ; some constraint on the hints, can try different things here. on 2x2 4 is the smallest p
        (assert (<= (count identity hints) max-desired-hints))
        ; primary solution should actually be a solution
        (assert (board-solved? cells))
        ; and the solution must be unique, which we check by saying:
        (assert
          (forall
            ; for every alternate solution...
            (symbolics alt-cells)
            (=>
              (&&
                ; ...if it's a well-formed solution...
                (apply && alt-asserts)
                ; ...and if it matches the primary solution on the hint cells...
                (apply && (map (λ (c a h) (=> h (equal? c a))) cells alt-cells hints))
                ; ...and if it's a solution...
                (board-solved? alt-cells))
              ; then it better be equal to the primary solution
              (apply && (map equal? cells alt-cells)))))
        ))))

  (define hints* (evaluate hints soln))
  (define cells* (evaluate cells soln))

  (define answer (evaluate cells soln))
  (define puzzle (map (λ (c h) (and h c)) answer (evaluate hints soln)))
  (printf "puzzle:\n")
  (print-puzzle puzzle)
  (printf "primary solution:\n")
  (print-puzzle (evaluate cells soln))

  puzzle)

; make a puzzle!
(define puzzle (generate-puzzle))

; solving it produces the same solution that was created during generation
(printf "if we try solving again:\n")
(print-puzzle (solve-puzzle puzzle))

; and since the solution is guaranteed unique, if we try to find two different solutions it should fail
(define cells1 (map (λ (c) (or c (symbolic-cell 0))) puzzle))
(define cells2 (map (λ (c) (or c (symbolic-cell 0))) puzzle))
(define validate-soln
  (solve
    (begin
      (assert (board-solved? cells1))
      (assert (board-solved? cells2))
      (assert (not (equal? cells1 cells2)))
      )))
(printf "unique solution? ~a\n" (unsat? validate-soln))

