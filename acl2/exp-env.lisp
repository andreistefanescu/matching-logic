;;; syntax of programs and configurations

(defun expp (e)
  (case-match e
    (('+ e1 e2) (and (expp e1) (expp e2)))
    (a (or (symbolp a)
	   (integerp a)))))

(defun iseval (e)
  (integerp e))

(defun freezerp (f)
  (case-match f
    (('+-HOLE e) (expp e))
    (('HOLE-+ e) (expp e))))

(defun kitemp (k)
  (or (expp k) (freezerp k)))

(defun klistp (k)
  (or (not k)
      (and (consp k)
	   (kitemp (car k))
	   (klistp (cdr k)))))

(defun envp (e)
  (or (not e)
      (and (symbolp (caar e))
	   (integerp (cdar e))
	   (envp (cdr e)))))

(defun cfgp (k)
  (and (consp k) (klistp (car k)) (envp (cdr k))))


;; destructuring - patterns have 'x to test equality,
;; & in a list to capture rest,
;; any other symbol binds.

(defmacro astep (before after &rest conds)
  `(case-match kbefore (,before (and ,@conds (equal kafter ,after)))))

(defun stepped (kbefore kafter)
  (or (astep ((('+ e1 e2) . rest) . env) `((,e1 (HOLE-+ ,e2) . ,rest) . ,env))
      (astep ((('+ e1 e2) . rest) . env) `((,e2 (+-HOLE ,e1) . ,rest) . ,env))
      (astep ((e1 ('HOLE-+ e2) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env) (expp e1))
      (astep ((e2 ('+-HOLE e1) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env) (expp e2))
      (astep ((v . rest) . env) `((,(cdr (assoc v env)) . ,rest) . ,env) (symbolp v) (assoc v env))
      (astep ((('+ i1 i2) . rest) . env) `((,(+ i1 i2) . ,rest) . ,env) (integerp i1) (integerp i2))))

;; had to add for the following theorem to go through.
;; can this be found automatically?
(defthm env-lookup-exp
  (implies (and (envp e) (assoc v e))
	   (expp (cdr (assoc v e)))))

(defthm step-wf
  (implies (and (cfgp before) (stepped before after))
	   (cfgp after)))

(defun hstep (cfg)
  (let ((kseq (car cfg))
	(env (cdr cfg)))
    (case-match kseq
      ((('+ e1 e2) . rest)
       (if (integerp e1)
	   (if (integerp e2)
	       `((,(+ e1 e2) . ,rest) . ,env)
	     `((,e2 (+-HOLE ,e1) . ,rest) . ,env))
	 `((,e1 (HOLE-+ ,e2) . ,rest) . ,env)))
      ((k1 . rest)
       (cond
	((symbolp k1)
	 (let ((v (cdr (assoc k1 env))))
	   (and v `((,v . ,rest) . ,env))))
	((integerp k1)
	 (case-match rest
	   ((('HOLE-+ e2) . rrest) `(((+ ,k1 ,e2) . ,rrest) . ,env))
	   ((('+-HOLE e1) . rrest) `(((+ ,e1 ,k1) . ,rrest) . ,env)))))))))
		 
(defun step-good (before)
  (let ((after (hstep before)))
    (or (not after) (stepped before after))))

(defthm hstep-sound
  (implies (cfgp cfg)
	   (step-good cfg)))

(defun steps (n cfg)
  (let ((next (hstep cfg)))
    (if (and (integerp n) (> n 0) next)
	(steps (- n 1) next)
      cfg)))

;;; End of the definitions I think would be automatically generated

;; Test execution
(steps 100 '(((+ x (+ 5 y))) . ((x . 10) (y . 100))))
;==> ((115) (X . 10) (Y . 100))

;;; Now, try to prove a few things to see if it's usable for that.

;; first, try to characterize configurations actually reached during
;; program execution, and show the tighter set is closed under step:

(defun freezerlistp (k)
  (or (not k)
      (and (freezerp (car k)) (freezerlistp (cdr k)))))

(defun eval-klistp (k)
  (and (consp k) (expp (car k)) (freezerlistp (cdr k))))
      
(defun eval-cfg (k)
  (and (eval-klistp (car k)) (envp (cdr k))))

(defthm step-preserve
  (implies (and (eval-cfg before) (stepped before after))
	   (eval-cfg after)))

;; second, prove a progress lemma that on this set
;; evaluation only once we have a value,
;; or hit a bad lokup

(defun done-or-stuck (k)
  (let ((klist (car k))
	(env (cdr k)))
    (or (case-match klist ((i) (integerp i)))
	(case-match klist ((v . &) (and (symbolp v) (not (assoc v env))))))))

;; needed for the progress theorem
(defthm env-lookup-missing
  (implies (and (envp env) (not (cdr (assoc v env))))
	   (not (assoc v env))))

;; progress
(defthm progress
  (implies (eval-cfg cfg) (or (hstep cfg) (done-or-stuck cfg)))
  :rule-classes nil
  )