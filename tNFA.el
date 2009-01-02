
;;; tNFA.el --- tagged non-deterministic finite-state automata package


;; Copyright (C) 2008 Toby Cubitt

;; Author: Toby Cubitt <toby-predictive@dr-qubit.org>
;; Version: 0.1
;; Keywords: TNFA, NFA, tagged, non-deterministic, finite state, automata
;; URL: http://www.dr-qubit.org/emacs.php


;; This file is NOT part of Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
;; MA 02110-1301, USA.


;;; Commentary:
;;


;;; Change Log:
;;
;; Version 0.1
;; * initial version



;;; Code:

(eval-when-compile (require 'cl))

(require 'queue)
(provide 'tNFA)


;;; ================================================================
;;;                    Data structures

;;; ----------------------------------------------------------------
;;;                    tagged NFA states

(defstruct
  (tNFA-state
   (:constructor nil)
   (:constructor tNFA-state-create-initial
		 (NFA-state num-tags min-tags max-tags
		  &aux (tags (tNFA-tags-create num-tags min-tags max-tags))))
   (:constructor tNFA-state-create (NFA-state tags))
   (:copier nil))
  NFA-state tags)

(defmacro tNFA-state-id (state)
  `(tNFA-NFA-state-id (tNFA-state-NFA-state ,state)))

(defmacro tNFA-state-type (state)
  `(tNFA-NFA-state-type (tNFA-state-NFA-state ,state)))

(defmacro tNFA-state-label (state)
  `(tNFA-NFA-state-label (tNFA-state-NFA-state ,state)))

(defmacro tNFA-state-in-degree (state)
  `(tNFA-NFA-state-in-degree (tNFA-state-NFA-state ,state)))

(defmacro tNFA-state-next (state)
  `(tNFA-NFA-state-next (tNFA-state-NFA-state ,state)))

(defmacro tNFA-state-count (state)
  `(tNFA-NFA-state-count (tNFA-state-NFA-state ,state)))



;;; ----------------------------------------------------------------
;;;                         NFA states

(declare (special NFA--state-id))

(defstruct
  (tNFA-NFA-state
   (:type vector)
   (:constructor nil)
   (:constructor tNFA-NFA-state-create
		 (&optional type label next
		  &aux
		  (in-degree 0)
		  (count 0)
		  (id (incf NFA--state-id))
		  (dummy (when next
			   (setf (tNFA-NFA-state-count next)
				 (incf (tNFA-NFA-state-in-degree next)))))))
   (:constructor tNFA-NFA-state-create-branch
		 (&rest next
		  &aux
		  (type 'branch)
		  (in-degree 0)
		  (count 0)
		  (id (incf NFA--state-id))))
   (:constructor tNFA-NFA-state-create-tag
		 (tag &optional next
		  &aux
		  (type 'tag)
		  (label (progn (message "%d" tag) tag))
		  (in-degree 0)
		  (count 0)
		  (id (incf NFA--state-id))
		  (dummy (when next
			   (setf (tNFA-NFA-state-count next)
				 (incf (tNFA-NFA-state-in-degree next)))))))
   (:copier nil))
  id type label in-degree
  count tNFA-state  ; used internally in NFA evolution algorithms
  next)

(defalias 'tNFA-NFA-state-tag 'tNFA-NFA-state-label)

(defmacro tNFA-NFA-state-tags (state)
  `(tNFA-state-tags (tNFA-NFA-state-tNFA-state ,state)))


(defun tNFA-NFA-state-patch (attach state)
  "Patch STATE onto ATTACH. Return value is meaningless."
  (setf (tNFA-NFA-state-type attach)  (tNFA-NFA-state-type state)
	(tNFA-NFA-state-label attach) (tNFA-NFA-state-label state)
	(tNFA-NFA-state-next attach)  (tNFA-NFA-state-next state)
	(tNFA-NFA-state-count state)  (incf (tNFA-NFA-state-in-degree state))
	))


(defun tNFA-NFA-state-make-epsilon (state next)
  "Create an epsilon transition from STATE to NEXT."
  (setf (tNFA-NFA-state-type state)  'epsilon
	(tNFA-NFA-state-label state) nil
	(tNFA-NFA-state-next state)  next
	(tNFA-NFA-state-count next)  (incf (tNFA-NFA-state-in-degree next))))


(defun tNFA-NFA-state-make-branch (state next)
  "Create a branch from STATE to all states in NEXT list."
  (setf (tNFA-NFA-state-type state)  'branch
	(tNFA-NFA-state-label state) nil
	(tNFA-NFA-state-next state)  next)
  (dolist (n next)
    (setf (tNFA-NFA-state-count n) (incf (tNFA-NFA-state-in-degree n)))))



;;; ----------------------------------------------------------------
;;;                        NFA fragments

(defstruct
  (NFA-fragment
   (:type vector)
   (:constructor nil)
   (:constructor NFA-fragment-create (initial final))
   (:copier nil))
  initial final)


(defun NFA-fragment-patch (frag1 frag2)
  "Patch FRAG2 onto end of FRAG1. Return value is meaningless."
  (tNFA-NFA-state-patch (NFA-fragment-final frag1) (NFA-fragment-initial frag2))
  (setf (NFA-fragment-final frag1) (NFA-fragment-final frag2)))



;;; ----------------------------------------------------------------
;;;                      tag tables

(defun tNFA-tags-create (num-tags min-tags max-tags)
  "Construct a new tags table."
  (let ((vec (make-vector num-tags nil)))
    (dolist (tag min-tags)
      (aset vec tag (cons -1 'min)))
    (dolist (tag max-tags)
      (aset vec tag (cons -1 'max)))
    vec))


(defun tNFA-tags-copy (tags)
  "Return a copy of TAGS table."
  (let* ((len (length tags))
	 (vec (make-vector len nil)))
    (dotimes (i len)
      (aset vec i (cons (car (aref tags i))
			(cdr (aref tags i)))))
    vec))


(defmacro tNFA-tags-set (tags tag val)
  "Set value of TAG in TAGS table to VAL."
  `(setcar (aref ,tags ,tag) ,val))


(defmacro tNFA-tags-get (tags tag)
  "Get value of TAG in TAGS table."
  `(car (aref ,tags ,tag)))


(defmacro tNFA-tags-type (tags tag)
  "Return the symbol `min' if TAG in TAGS table is a minimize tag,
`max' if it is a maximize tag."
  `(cdr (aref ,tags ,tag)))


(defun tNFA-tags< (val tag tags)
  "Return non-nil if VAL takes precedence over the value of TAG in TAGS table,
otherwise return nil."
  (setq tag (aref tags tag))
  (or (and (eq (cdr tag) 'min)
	   (< val (car tag)))
    ;;(and (eq (cdr tag) 'max)
	   (> val (car tag));)
	   ))



;;; ----------------------------------------------------------------
;;;                      DFA states

(defstruct
  (tNFA-DFA-state
   :named
   (:constructor nil)
   (:constructor tNFA--DFA-state-create
		 (list pool
		  &key (test 'eq)
		  &aux
		  (transitions (make-hash-table :test test))))
   (:constructor tNFA-DFA-state-create-failed ())
   (:copier nil))
  list transitions wildcard match pool)


(defun* tNFA-DFA-state-create (state-list state-pool &key (test 'eq))
  ;; create DFA state and add it to the state pool
  (let ((DFA-state (tNFA--DFA-state-create
		    state-list state-pool :test test)))
    (puthash state-list DFA-state (tNFA-DFA-state-pool DFA-state))

    (dolist (state state-list)
      ;; if state in state list is...
      (cond
       ;; literal state: add literal transition
       ((eq (tNFA-state-type state) 'literal)
	(puthash (tNFA-state-label state) t
		 (tNFA-DFA-state-transitions DFA-state)))

       ;; character alternative: add transitions for all alternatives
       ((eq (tNFA-state-type state) 'char-alt)
	(dolist (c (tNFA-state-label state))
	  (puthash c t (tNFA-DFA-state-transitions DFA-state))))

       ;; wildcard or negated character alternative: add wildcard transistion
       ((or (eq (tNFA-state-type state) 'wildcard)
	    (eq (tNFA-state-type state) 'neg-char-alt))
	(setf (tNFA-DFA-state-wildcard DFA-state) t))

       ;; match state: set match tags
       ((eq (tNFA-state-type state) 'match)
	(setf (tNFA-DFA-state-match DFA-state)
	      (tNFA-state-tags state)))))

    ;; return constructed state
    DFA-state))


(defun* tNFA-DFA-state-create-initial (initial-state &key (test 'eq))
  ;; create initial DFA state from initial tNFA state INITIAL-STATE
  (tNFA-DFA-state-create (list initial-state)
			 (make-hash-table :test 'equal)
			 :test test))


(defun tNFA-DFA-state-failed-p (state)
  "Return t if STATE is a failed match, otherwise returns nil."
  (null (tNFA-DFA-state-list state)))

(defalias 'tNFA-DFA-state-match-p 'tNFA-DFA-state-match
  "Return non-nil if STATE is a matching state, otherwise returns nil.")




;;; ================================================================
;;;                        Regexp -> tNFA

(defun* tNFA-from-regexp (regexp &key (test 'eq))
  "Create a tagged NFA that recognizes the regular expression REGEXP.

Back-references and non-greedy postfix operators are *not* supported, and the
matches are always anchored, so `$' and `^' lose their special meanings.

The return value is the initial state of the tagged NFA.

The :test keyword argument specifies how to test whether two
individual elements of a string are identical. The default is `eq'."

  ;; convert regexp to list, build NFA, and return initial state
  (declare (special NFA--state-id))
  (destructuring-bind (fragment num-tags min-tags max-tags regexp)
      (let ((NFA--state-id -1))
	(tNFA--from-regexp (append regexp nil) 0 '() '() 'top-level))
    (if regexp
	(error "Syntax error in regexp: missing \"(\"")
      (setf (tNFA-NFA-state-type (NFA-fragment-final fragment)) 'match)
      (tNFA-DFA-state-create-initial
       (tNFA-state-create-initial
	(NFA-fragment-initial fragment) num-tags min-tags max-tags)
       :test test)
      )))



(defun tNFA--from-regexp (regexp num-tags min-tags max-tags
				 &optional top-level)
  (let* ((new (tNFA-NFA-state-create))
	 (fragment-stack (list (NFA-fragment-create new new)))
	 fragment attach token type)

    (catch 'constructed
      (while t
	(setq regexp (NFA-regexp-next-token regexp)
	      type   (nth 0 regexp)
	      token  (nth 1 regexp)
	      regexp (nth 2 regexp))
	(setq fragment nil)

	;; ----- construct new fragment -----
	(cond
	 ;; syntax error: missing )
	 ((and (null type) (not top-level))
	  (error "Syntax error in regexp: extra \"(\" or missing \")\""))

	 ;; syntax error: extra )
	 ((and (eq type 'shy-group-end) top-level)
	  (error "Syntax error in regexp: extra \")\" or missing \"(\""))

	 ;; syntax error: postfix operator not after atom
	 ((or (eq type 'postfix*) (eq type 'postfix+) (eq type 'postfix?))
	  (error "Syntax error in regexp: unexpected \"%s\""
		 (char-to-string token)))

	 ;; regexp atom: construct new literal fragment
	 ((or (eq type 'literal) (eq type 'wildcard)
	      (eq type 'char-alt) (eq type 'neg-char-alt))
	  (setq new (tNFA-NFA-state-create type token (tNFA-NFA-state-create))
		fragment (NFA-fragment-create new (tNFA-NFA-state-next new))))

	 ;; shy subgroup start: recursively construct subgroup fragment
	 ((eq type 'shy-group-start)
	  (setq new (tNFA--from-regexp regexp num-tags min-tags max-tags)
		num-tags (nth 1 new)
		min-tags (nth 2 new)
		max-tags (nth 3 new)
		regexp   (nth 4 new)
		fragment (nth 0 new)))

	 ;; subgroup start: recursively construct subgroup fragment, attaching
	 ;;                 minimize tag to the front
	 ((eq type 'group-start)
	  (setq new (tNFA-NFA-state-create))
	  (setq fragment
		(NFA-fragment-create
		 (tNFA-NFA-state-create-tag
		  (car (push (1- (incf num-tags)) min-tags))
		  new)
		 new))
	  (setq new (tNFA--from-regexp regexp num-tags min-tags max-tags)
		num-tags (nth 1 new)
		min-tags (nth 2 new)
		max-tags (nth 3 new)
		regexp   (nth 4 new)
		new      (nth 0 new))
	  (NFA-fragment-patch fragment new))


	 ;; end of regexp or subgroup: ...
	 ((or (null type) (eq type 'shy-group-end) (eq type 'group-end))

	  ;; if fragment-stack contains only one fragment...
	  (cond
	   ((null (nth 1 fragment-stack))
	    ;; if ending a group, add a maximize tag to end of fragment
	    (when (eq type 'group-end)
	      (setq new (tNFA-NFA-state-create)
		    fragment (NFA-fragment-create
			      (tNFA-NFA-state-create-tag
			       (car (push (1- (incf num-tags)) max-tags))
			       new)
			      new))
	      (NFA-fragment-patch (car fragment-stack) fragment))
	    ;; throw fragment up to recursion level above
	    (throw 'constructed
		   (list (car fragment-stack)
			 num-tags min-tags max-tags regexp)))

	   ;; if fragment-stack contains multiple alternation fragments,
	   ;; attach them all together
	   ;;
	   ;;          .--fragment--.
	   ;;         /              \
	   ;;        /----fragment----\
	   ;;       /                  \
	   ;;   ---o------fragment------o--->
	   ;;       \        .         /
	   ;;        \       .        /
	   ;;                .
	   (t
	    ;; create a new fragment containing start and end of alternation;
	    ;; if ending a group, make end of alternation a maximize tag
	    (setq fragment
		  (NFA-fragment-create
		   (tNFA-NFA-state-create-branch)
		   (if (eq type 'group-end)
		       (tNFA-NFA-state-create-tag
			(car (push (1- (incf num-tags)) max-tags))
			(tNFA-NFA-state-create))
		     (tNFA-NFA-state-create))))
	    ;; patch alternation fragments into new fragment
	    (dolist (frag fragment-stack)
	      (push (NFA-fragment-initial frag)
		    (tNFA-NFA-state-next (NFA-fragment-initial fragment)))
	      (setf (tNFA-NFA-state-count (NFA-fragment-initial frag))
		    (incf (tNFA-NFA-state-in-degree
			   (NFA-fragment-initial frag))))
	      (tNFA-NFA-state-make-epsilon (NFA-fragment-final frag)
				      (NFA-fragment-final fragment)))
	    ;; if ending a group, step the end of the fragment along one link,
	    ;; to the blank state linked from the tag
	    (when (eq type 'group-end)
	      (setf (NFA-fragment-final fragment)
		    (tNFA-NFA-state-next (NFA-fragment-final fragment))))
	    ;; throw constructed fragment up to recursion level above
	    (throw 'constructed
		   (list fragment num-tags min-tags max-tags regexp)))
	   ))

	 ;; | alternation: start new fragment
	 ((eq type 'alternation)
	  (setq new (tNFA-NFA-state-create))
	  (push (NFA-fragment-create new new) fragment-stack)))


	;; ----- attach new fragment -----
	(when fragment
	  (setq attach (NFA-fragment-final (car fragment-stack)))
	  (if (or (eq (car regexp) ?*)
		  (eq (car regexp) ?+)
		  (eq (car regexp) ??))
	      (if (eq type 'alternation)
		  (error "Syntax error in regexp: unexpected \"%s\""
			 (char-to-string token))

		;; if next token is a postfix operator, splice new fragment
		;; into NFA as appropriate
		(setq regexp (NFA-regexp-next-token regexp)
		      type   (nth 0 regexp)
		      token  (nth 1 regexp)
		      regexp (nth 2 regexp))
		(setq new (tNFA-NFA-state-create))

		(cond

		 ;;    .--fragment--.
		 ;;   /              \
		 ;;   \        ______/
		 ;;    \      /
		 ;;  ---attach-----new---
		 ;;
		 ((eq type 'postfix*)
		  (tNFA-NFA-state-make-branch
		   attach (list (NFA-fragment-initial fragment) new))
		  (tNFA-NFA-state-make-epsilon
		   (NFA-fragment-final fragment) attach)
		  (setf (NFA-fragment-final (car fragment-stack)) new))

		 ;;      .----.
		 ;;     /      \
		 ;;    /        \
		 ;;    \        /
		 ;;  ---fragment-----new---
		 ;;
		 ((eq type 'postfix+)
		  (tNFA-NFA-state-patch
		   attach (NFA-fragment-initial fragment))
		  (tNFA-NFA-state-make-branch
		   (NFA-fragment-final fragment) (list attach new))
		  (setf (NFA-fragment-final (car fragment-stack)) new))

		 ;;            .--fragment--.
		 ;;           /              \
		 ;;  ---attach                new---
		 ;;           \______________/
		 ;;
		 ((eq type 'postfix?)
		  (tNFA-NFA-state-make-branch
		   attach (list (NFA-fragment-initial fragment) new))
		  (tNFA-NFA-state-make-epsilon
		   (NFA-fragment-final fragment) new)
		  (setf (NFA-fragment-final (car fragment-stack)) new))
		 ))


	    ;; if next token is not a postfix operator, attach new fragment
	    ;; onto end of current NFA fragment
	    (NFA-fragment-patch (car fragment-stack) fragment)))
	))  ; end of infinite loop and catch
    ))



(defun NFA-regexp-next-token (regexp)
  ;; if regexp is empty, return null values for next token type, token and
  ;; remaining regexp
  (if (null regexp)
      (list nil nil nil)

    (let ((token (pop regexp))
	  (type 'literal))  ; assume token is literal initially
      (cond

       ;; [: gobble up to closing ]
       ((eq token ?\[)
	;; character alternatives are stored in lists
	(setq token '())
	(cond
	 ;; gobble ] appearing straight after [
	 ((eq (car regexp) ?\]) (push (pop regexp) token))
	 ;; gobble ] appearing straight after [^
	 ((and (eq (car regexp) ?^) (eq (nth 1 regexp) ?\]))
	  (push (pop regexp) token)
	  (push (pop regexp) token)))
	;; gobble everything up to closing ]
	(while (not (eq (car regexp) ?\]))
	  (push (pop regexp) token)
	  (unless regexp
	    (error "Syntax error in regexp: missing \"]\"")))
	(pop regexp)  ; dump closing ]
	(if (not (eq (car (last token)) ?^))
	    (setq type 'char-alt)
	  (setq type 'neg-char-alt)
	  (setq token (butlast token))))

       ;; ]: syntax error (always gobbled when parsing [)
       ((eq token ?\])
	(error "Syntax error in regexp: missing \"[\""))

       ;; . * + ?: set appropriate type
       ((eq token ?*) (setq type 'postfix*))
       ((eq token ?+) (setq type 'postfix+))
       ((eq token ??) (setq type 'postfix?))
       ((eq token ?.) (setq type 'wildcard))

       ;; \: look at next character
       ((eq token ?\\)
	(unless (setq token (pop regexp))
	  (error "Syntax error in regexp: missing character after \"\\\""))
	(cond
	 ((eq token ?|) (setq type 'alternation))
	 ((and (eq token ?\() (eq (car regexp) ??))
	  (setq type 'shy-group-start)
	  (pop regexp))
	 ((and (eq token ?\)) (eq (car regexp) ??))
	  (setq type 'shy-group-end)
	  (pop regexp))
	 ((eq token ?\() (setq type 'group-start))
	 ((eq token ?\)) (setq type 'group-end))))
       )

      ;; return first token type, token, and remaining regexp
      (list type token regexp))))



;;; ================================================================
;;;                     tNFA evolution

(defun tNFA-next-state (DFA-state chr pos)
  (let (state)
    ;; if there is a transition for character CHR...
    (cond
     ((setq state (gethash chr (tNFA-DFA-state-transitions DFA-state)))
      ;; if next state has not already been computed, do so
      (unless (tNFA-DFA-state-p state)
	(setq state (tNFA--DFA-next-state DFA-state chr pos nil))
	(puthash chr state (tNFA-DFA-state-transitions DFA-state))))

     ;; if there's a wildcard transition...
     ((setq state (tNFA-DFA-state-wildcard DFA-state))
      ;; if next state has not already been computed, do so
      (unless (tNFA-DFA-state-p state)
	(setq state (tNFA--DFA-next-state DFA-state chr pos t))
	(setf (tNFA-DFA-state-wildcard DFA-state) state))))
    state))



(defun tNFA--DFA-next-state (DFA-state chr pos wildcard)
  (let (state-list state)
    ;; add all states reached by a CHR transition from DFA-STATE to state list
    (if wildcard
	(dolist (state (tNFA-DFA-state-list DFA-state))
	  (when (or (eq (tNFA-state-type state) 'wildcard)
		    (and (eq (tNFA-state-type state) 'neg-char-alt)
			 (not (memq chr (tNFA-state-label state)))))
	    (push (tNFA-state-create (tNFA-state-next state)
				     (tNFA-tags-copy (tNFA-state-tags state)))
		  state-list)))
      (dolist (state (tNFA-DFA-state-list DFA-state))
	(when (or (and (eq (tNFA-state-type state) 'literal)
		       (eq chr (tNFA-state-label state)))
		  (and (eq (tNFA-state-type state) 'char-alt)
		       (memq chr (tNFA-state-label state)))
		  (and (eq (tNFA-state-type state) 'neg-char-alt)
		       (not (memq chr (tNFA-state-label state))))
		  (eq (tNFA-state-type state) 'wildcard))
	  (push (tNFA-state-create (tNFA-state-next state)
				   (tNFA-tags-copy (tNFA-state-tags state)))
		state-list))))

    ;; if state list is empty, return empty, failure DFA state
    (when state-list
      ;; otherwise, construct new DFA state and add it to the pool if it's not
      ;; already there
      (setq state-list (tNFA-epsilon-boundary state-list (1+ pos)))
      (setq state
	    (or (gethash state-list (tNFA-DFA-state-pool DFA-state))
		(tNFA-DFA-state-create
		 state-list
		 (tNFA-DFA-state-pool DFA-state)
		 :test
		 (hash-table-test (tNFA-DFA-state-transitions DFA-state)))))
      ;; return next state
      state)))



(defun tNFA-epsilon-boundary (state-set pos)
  ;; Return the tagged epsilon-closure of the tNFA states listed in STATE-SET,
  ;; that is the set of all states that can be reached via only epsilon
  ;; transitions from some state in STATE-SET. (This includes all states in
  ;; STATE-SET itself.)
  (let ((queue (queue-create))
	(result '())
	(seen '())
	state next tags)
    ;; temporarily link the NFA states to their corresponding tNFA states, and
    ;; add them to the queue
    (dolist (t-state state-set)
      (setf state (tNFA-state-NFA-state t-state)
	    (tNFA-NFA-state-tNFA-state state) t-state)
      (push t-state seen)
      (queue-enqueue queue state))

    (while (setq state (queue-dequeue queue))
      (cond
       ;; branch or epsilon: add next states as necessary, copying tags across
       ((or (eq (tNFA-NFA-state-type state) 'branch)
	    (eq (tNFA-NFA-state-type state) 'epsilon))
	(dolist (next (if (eq (tNFA-NFA-state-type state) 'epsilon)
			  (list (tNFA-NFA-state-next state))
			(tNFA-NFA-state-next state)))
	  (unless (tNFA-NFA-state-tNFA-state next)
	    (setf (tNFA-NFA-state-tNFA-state next)
		  (tNFA-state-create
		   next (tNFA-tags-copy (tNFA-NFA-state-tags state))))
	    (push (tNFA-NFA-state-tNFA-state next) seen)
	    ;; if next state hasn't already been seen in-degree times, add it
	    ;; to the end of the queue
	    (if (/= (decf (tNFA-NFA-state-count next)) 0)
		(queue-enqueue queue next)
	      ;; if it has now been seen in-degree times, reset count and add
	      ;; it back to the front of the queue
	      (setf (tNFA-NFA-state-count next)
		    (tNFA-NFA-state-in-degree next))
	      (queue-prepend queue next)))))

       ;; tag: add next state if necessary, updating tags if necessary
       ((eq (tNFA-NFA-state-type state) 'tag)
	(setq next (tNFA-NFA-state-next state))
	;; if next state is not already in results list, or it is already in
	;; results but new tag value takes precedence...
	(when (or (not (tNFA-NFA-state-tNFA-state next))
		  (tNFA-tags< pos (tNFA-NFA-state-tag state)
			      (tNFA-NFA-state-tags next)))
	  ;; if next state is already in results, update tag value
	  (if (tNFA-NFA-state-tNFA-state next)
	      (tNFA-tags-set (tNFA-NFA-state-tags next)
			     (tNFA-NFA-state-tag state) pos)
	    ;; if state is not already in results, copy tags, updating tag
	    ;; value, and add next state to results list
	    (setq tags (tNFA-tags-copy (tNFA-NFA-state-tags state)))
	    (tNFA-tags-set tags (tNFA-NFA-state-tag state) pos)
	    (setf (tNFA-NFA-state-tNFA-state next)
		  (tNFA-state-create next tags))
	    (push (tNFA-NFA-state-tNFA-state next) seen))
	  ;; if next state hasn't already been seen in-degree times, add it to
	  ;; the end of the queue
	  (if (/= (decf (tNFA-NFA-state-count next)) 0)
	      (queue-enqueue queue next)
	    ;; if it has now been seen in-degree times, reset count and add it
	    ;; back to the front of the queue
	    (setf (tNFA-NFA-state-count next) (tNFA-NFA-state-in-degree next))
	    (queue-prepend queue next))))

       ;; anything else is a non-epsilon-transition state, so add it to result
       (t (push (tNFA-NFA-state-tNFA-state state) result))
       ))

    ;; reset temporary NFA state link and count
    (dolist (state seen)
      (setf (tNFA-NFA-state-tNFA-state (tNFA-state-NFA-state state)) nil
	    (tNFA-NFA-state-count (tNFA-state-NFA-state state))
	      (tNFA-NFA-state-in-degree (tNFA-state-NFA-state state))))
    ;; sort result states
    (sort result (lambda (a b) (< (tNFA-state-id a) (tNFA-state-id b))))
    ))



;;; ================================================================
;;;                       tNFA matching

(defun tNFA-regexp-match (regexp string)
  "Return non-nil if STRING matches REGEXP, nil otherwise.
Sets the match data if there was a match; see `match-beginning',
`match-end' and `match-string'."

  (let ((tNFA (tNFA-from-regexp regexp))
	(i -1) tags match-data group-stack (grp 0))

    ;; evolve tNFA according to characters of STRING
    (catch 'fail
      (dolist (chr (append string nil))
	(unless (setq tNFA (tNFA-next-state tNFA chr (incf i)))
	  (throw 'fail nil)))

      ;; if REGEXP matched...
      (when (setq tags (tNFA-DFA-state-match tNFA))
	(setq match-data (make-list (+ (length tags) 2) nil))
	;; set match data
	(setf (nth 0 match-data) 0
	      (nth 1 match-data) (length string))
	;; set group match data if there were any groups
	(dotimes (i (length tags))
	  (if (eq (tNFA-tags-type tags i) 'max)
	      (unless (= (tNFA-tags-get tags i) -1)
		(setf (nth (1+ (* 2 (pop group-stack))) match-data)
		      (tNFA-tags-get tags i)))
	    (incf grp)
	    (unless (= (tNFA-tags-get tags i) -1)
	      (push grp group-stack)
	      (setf (nth (* 2 grp) match-data)
		    (tNFA-tags-get tags i)))))
	(set-match-data match-data)
	tags))))



(defun tNFA-tags-to-groups (tags)
  "Convert TAGS table to a list of indices of group matches.
The nth element of the list is a cons cell, whose car is the
starting index of the nth group and whose cdr is its end
index. If a group didn't match, the corresponding list element
will by null."
  (let ((groups (make-list (/ (length tags) 2) nil))
	group-stack
	(grp 0))
    (dotimes (i (length tags))
      (if (eq (tNFA-tags-type tags i) 'max)
	  (unless (= (tNFA-tags-get tags i) -1)
	    (setf (nth (caar group-stack) groups)
		  (cons (cdr (pop group-stack)) (tNFA-tags-get tags i))))
	(unless (= (tNFA-tags-get tags i) -1)
	  (push (cons grp (tNFA-tags-get tags i)) group-stack))
	(incf grp)))
    groups))


;;; tNFA.el ends here
