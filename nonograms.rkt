; A Nonograms solver/validator/generator to illustrate solving 2QBF problems with Rosette.
; This is not meant to be an efficient or high quality generator;
; it's intended to illustrate how to use Rosette.
;
; The Rosette library can be found at http://emina.github.io/rosette/
;
; author: Eric D Butler (edbutler@cs.washignton.edu)
; date: 2017 February 22
; license: MIT

#lang rosette

(require json)

; we want theory of integers, not bitvectors (required for forall)
(current-bitwidth #f)

; board spec, the hints for all rows and columns
; row-hints: (listof (listof integer?)), col-hints: (listof (listof integer?))
(struct spec (row-hints col-hints) #:transparent)
; a board, spec + array of cells, row major
; spec: spec?, cells: (vectorof boolean?)
(struct board (spec cells) #:transparent)
; a single row/column of a board, both hints and state
; hints: (listof integer?), cells: (listof boolean?)
(struct line (hints cells) #:transparent)

; board?, integer?, integer? -> boolean?
; references a cell at the given column x and row y
(define (board-ref brd x y)
  (define width (length (spec-col-hints (board-spec brd))))
  (vector-ref (board-cells brd) (+ (* width y) x)))

; board? -> (listof line?)
; every line of a given board
(define (board-all-lines brd)
  (match-define (board (spec row-hints col-hints) cells) brd)
  (define width (length col-hints))
  (define height (length row-hints))
  (append
    (for/list ([y height]
               [h row-hints])
      (line h (map (λ (x) (board-ref brd x y)) (range width))))
    (for/list ([x width]
               [h col-hints])
      (line h (map (λ (y) (board-ref brd x y)) (range height))))))

; board? -> string?
; makes a pretty terminal rendering of a board. requires unicode terminal support.
(define (pretty-format-board brd)
  (match-define (board (spec row-hints col-hints) cells) brd)
  (printf "~a\n" row-hints)
  (printf "~a\n" col-hints)
  (printf "~a ~a\n" (length row-hints) (length col-hints))
  (define (pretty-format-state s)
    (string-join (map (λ (c) (if c "█" " ")) s) "" #:before-first "║" #:after-last "║"))
  ; HACK assumes all lines returns the rows first
  (define horz (make-string (length col-hints) #\═))
  (define middle (map (compose pretty-format-state line-cells) (take (board-all-lines brd) (length row-hints))))
  (define header (string-append "╔" horz "╗"))
  (define footer (string-append "╚" horz "╝"))
  (string-join (append (cons header middle) (list footer)) "\n"))

; a segment is a location for a contiguous run of filled cells, definied by a start and end.
; the solver works by creating one symbolic segment for each hint of the appropriate length,
; guessing the starting index of the segment, and ensuring all segments are consistent with
; the board's symbolic cells.
; When generating, rather than generate a symbolic number of segments, we generate the maximum
; number of possible segments and then symbolically enable some of them. The used? field
; implements this concept. Segments only matter if used? is true.
; start: integer?, end: integer?, used?: boolean.
(struct segment (start end used?) #:transparent)

; segment?, (listof boolean?) -> boolean?
; returns true if the given set of segments is consistent with the given line.
(define (segments-consistent? segments cells)
  (apply &&
    (map
      (λ (i c)
        (equal? c (apply || (map (λ (s) (&& (segment-used? s) (<= (segment-start s) i) (< i (segment-end s)))) segments))))
      (range (length cells))
      cells)))

; integer?, integer? -> (and/c symbolic? term?)
; Shorthand for making symbolic integers in range [mn, mx] (inclusive).
(define (?? mn mx)
  (define-symbolic* i integer?)
  (assert (<= mn i))
  (assert (<= i mx))
  i)

; -> (and/c boolean? term?)
; Shorthand for symoblic booleans.
(define (!!)
  (define-symbolic* b boolean?)
  b)

; (listof boolean?), (listof integer?), integer? -> (and/c (listof segment?) term?)
; creates symbolic segments for a given line that are consistent with its hints, one per hint.
; (length all-hints) must be concrete (not symoblic) and >= num-hints (which may be symbolic)
(define (symbolic-segments cells all-hints num-hints)
  (define len (length cells))
  (define segments
    ; use fold instead of map because we need to reference the previous segment
    (foldl
      (λ (i h acc)
        (define-symbolic* s integer?)
        (define used? (< i num-hints))
        (define e (+ s h))
        (assert (>= s 0))
        (assert (<= e len))
        (unless (empty? acc)
          ; must have gap of at least one between segments
          (assert (=> used? (> s (segment-end (first acc))))))
        (cons (segment s e used?) acc))
      '()
      (range (length all-hints))
      all-hints))
  ; assert these segments are consistent with the board hints
  (assert (segments-consistent? segments cells))
  segments)

; spec? -> (or/c board? #f)
(define (solve-puzzle spc)
  (match-define (spec row-hints col-hints) spc)
  (define width (length col-hints))
  (define height (length row-hints))
  ; fill out the board
  (define b (board spc (build-vector (* width height) (λ (_) (!!)))))
  ; guess the segments for each hint, this will also assert that the board is solved
  (for ([ln (board-all-lines b)])
    (match-define (line hints cells) ln)
    (symbolic-segments cells hints (length hints)))
  (define soln (time (solve (assert #t))))
  (and (sat? soln) (evaluate b soln)))

(define-syntax-rule (solver-assert* slvr expr)
  (let-values ([(e asrts) (with-asserts expr)])
    (when (boolean? e) (solver-assert slvr (list e)))
    (solver-assert slvr asrts)))

; Calculates whether the given board has a unique solution.
; Returns either 'unsolvable if no solutions,
; (list 'valid soln) if one solution (where soln is a board?), or
; (list 'invalid soln1 soln2) if multiple solutions (where both solns are board?).
(define (validate-puzzle spc)
  ; use the manual solving routines so we can use incremental solving.
  (define slvr (current-solver))
  (solver-clear slvr)

  (match-define (spec row-hints col-hints) spc)
  (define width (length col-hints))
  (define height (length row-hints))
  ; fill out the board
  (define b1 (board spc (build-vector (* width height) (λ (_) (!!)))))
  (define b2 (board spc (build-vector (* width height) (λ (_) (!!)))))
  ; guess the segments for each hint, this will also assert that the board is solved
  (solver-assert* slvr
    (for ([ln (board-all-lines b1)])
      (match-define (line hints cells) ln)
      (symbolic-segments cells hints (length hints))))
  (define soln (time (solver-check slvr)))
  (cond
   [(sat? soln)
    ; we found one solution, now find a second that is different to se if it's unique
    (solver-assert* slvr
      (for ([ln (board-all-lines b2)])
        (match-define (line hints cells) ln)
        (symbolic-segments cells hints (length hints))))
    (solver-assert* slvr (apply || (map (λ (x y) (not (equal? x y))) (vector->list (board-cells b1)) (vector->list (board-cells b2)))))
    (define soln2 (time (solver-check slvr)))
    (if (unsat? soln2)
        `(valid ,(evaluate b1 soln))
        `(invalid ,(evaluate b1 soln2) ,(evaluate b2 soln2)))]
   [else
    ; not solvable at all
    'unsolvable]))

; integer? -> integer?
; The maximum number of hints possible for any nonograms line of the given length.
; Longest possible line is all 1's, with minimal gaps in between.
(define (max-hints-for-length len)
  (quotient (add1 len) 2))

; integer? -> (listof integer?)
; creates symbolic hints for a single line, given the line length.
(define (symbolic-hints line-len)
  (define max-hints (max-hints-for-length line-len))
  (define (symbolic-hint i)
    ; hints are bounded by the line length and number of previous hints
    ; (e.g., first hint could be line-len, but last could only be 1).
    (?? 1 (- line-len (* 2 i))))
  (build-list max-hints symbolic-hint))

; integer?, integer? -> board?
; Generates an arbitrary but valid (unique solution) nonograms puzzle of the given dimensions.
(define (generate-puzzle width height)
  (define all-row-hints (build-list height (λ (_) (symbolic-hints width))))
  (define all-col-hints (build-list width (λ (_) (symbolic-hints height))))

  (define num-row-hints (build-list height (λ (_) (?? 0 (max-hints-for-length width)))))
  (define num-col-hints (build-list width (λ (_) (?? 0 (max-hints-for-length height)))))

  (define row-hints (map take all-row-hints num-row-hints))
  (define col-hints (map take all-row-hints num-row-hints))

  ; guess a primary solution
  (define cells (build-list (* width height) (λ (_) (!!))))
  (define b (board (spec row-hints col-hints) (list->vector cells)))

  ; primary solution must solve puzzle
  (for ([ln (board-all-lines b)]
        [all-hints (append all-row-hints all-col-hints)]
        [num-hints (append num-row-hints num-col-hints)])
    (match-define (line _ cells) ln)
    (symbolic-segments cells all-hints num-hints))

  ; guess an alternate solution
  (define alt-cells (build-list (* width height) (λ (_) (!!))))
  (define alt-board (board (spec row-hints col-hints) (list->vector alt-cells)))
  ; hold onto the asserts for solvability, can't use them until inside the (forall ...)
  (define-values (alt-segments alt-asserts)
    (with-asserts
      (for/list ([ln (board-all-lines alt-board)]
                 [all-hints (append all-row-hints all-col-hints)]
                 [num-hints (append num-row-hints num-col-hints)])
        (match-define (line _ cells) ln)
        (symbolic-segments cells all-hints num-hints))))

  ; alternate solution must be a solution only if it equals the primary solution,
  ; for all possible alternate solutions (this guarantees the primary solution is unique).
  (assert
    (forall (set-subtract (symbolics (cons alt-cells alt-segments)) (symbolics b))
      (=>
        (apply && alt-asserts)
        (apply && (map equal? alt-cells cells)))))

  ; some design constraints about the portion of cells that are filled
  (define min-cells (quotient (* width height) 4))
  (define max-cells (max width (* 3 (quotient (* width height) 4))))

  ; assert puzzle has at least _some_ stuff in it
  (define filled-cells (count identity cells))
  (printf "constraining puzzle to have between ~a and ~a filled cells\n" min-cells max-cells)
  (assert (>= filled-cells min-cells))
  (assert (<= filled-cells max-cells))

  (define soln
    (solve
      (assert #t)))
  (and (sat? soln) (evaluate b soln)))

; input-port? -> spec?
(define (json->spec f)
  (define jval (hash-ref (read-json f) 'hints))
  (spec (hash-ref jval 'rows) (hash-ref jval 'cols)))

(define command (make-parameter #f))

(command-line
 #:once-any
 [("-s" "--solve") "Solves a puzzle given through stdin in json format." (command 'solve)]
 [("-v" "--validate") "Validates that a puzzle given through stdin in json format has a unique solution." (command 'validate)]
 [("-g" "--generate") width height "Generate a random puzzle of the given dimensions." (command `(generate ,(string->number width) ,(string->number height)))])

(match (command)
 ['solve
  (define spc (json->spec (current-input-port)))
  (define brd (time (solve-puzzle spc)))
  (cond
   [brd
    (printf "~a\n" (pretty-format-board brd))]
   [else
    (printf "unsolvable!\n")])]
 ['validate
  (define spc (json->spec (current-input-port)))
  (match (time (validate-puzzle spc))
   [`(valid ,brd)
    (printf "~a\nBoard is valid, has a unique solution.\n" (pretty-format-board brd))]
   [`(invalid ,brd1 ,brd2)
    (printf "~a\n\n~a\nBoard is invalid, has multiple solutions.\n" (pretty-format-board brd1) (pretty-format-board brd2))]
   ['unsolvable
    (define col-hints (spec-col-hints spc))
    (define row-hints (spec-row-hints spc))
    (define (count-hints h) (apply + (append-map append h)))
    (printf "unsolvable!\nboard size: ~a ~a\ntotal hints: ~a ~a\n" (length col-hints) (length row-hints) (count-hints col-hints) (count-hints row-hints))])]
 [`(generate ,w ,h) #:when (and (integer? w) (integer? h))
  (define brd (time (generate-puzzle w h)))
  (printf "~a\n" (pretty-format-board brd))]
 [_
  (displayln "Invalid arguments. Use --help for arguments." (current-error-port))
  (exit 1)])

