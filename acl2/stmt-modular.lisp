;;; syntax of programs and configurations

(defun expp (e)
  (case-match e
    (('+ e1 e2) (and (expp e1) (expp e2)))
    (('++ a) (symbolp a))
    (a (or (and a (symbolp a))
	   (integerp a)))))

(mutual-recursion
 (defun stmtp (s)
   (case-match s
     (('while e stmts) (and (expp e) (stmtp stmts)))
     (('if e block1 block2) (and (expp e) (stmtp block1) (stmtp block2)))
     (('assign v e) (and (symbolp v) (expp e)))
     (('block . stmts) (stmtlistp stmts))
     (('eval e) (expp e))))
 (defun stmtlistp (b)
   (or (not b)
       (and (consp b) (stmtp (car b)) (stmtlistp (cdr b))))))

(defun isval (e)
  (integerp e))

(defun freezerp (f)
  (case-match f
    (('+-HOLE e) (expp e))
    (('HOLE-+ e) (expp e))
    (('if-HOLE block1 block2) (and (stmtp block1) (stmtp block2)))
    (('assign-HOLE v) (symbolp v))
    ('eval-HOLE t)
    ))

(defun kitemp (k)
  (or (expp k) (stmtp k) (freezerp k)))

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

(defthm env-lookup-int
  (implies (and (envp e) (assoc v e))
	   (integerp (cdr (assoc v e))))
  :rule-classes ((:type-prescription :typed-term (cdr (assoc v e)))))
(defthm env-put-int
  (implies (and (envp e) (symbolp v) (integerp x))
	   (envp (put-assoc-eql v x e))))


(defun cfgp (k)
  (and (consp k) (klistp (car k)) (envp (cdr k))))

;; destructuring - patterns have 'x to test equality,
;; & in a list to capture rest,
;; any other symbol binds.
(defun mk-rule-body (body conds)
  (case-match conds
    ((('let x e) . conds)
     `(let ((,x ,e)) ,(mk-rule-body body conds)))
    ((('let-assoc x v env) . conds)
     `(and (symbolp ,v) (assoc ,v ,env)
	   (let ((,x (cdr (assoc ,v ,env)))) ,(mk-rule-body body conds))))
    (nil body)
    ((c . conds) `(and ,c ,(mk-rule-body body conds)))))

(defmacro defrule (rule before after &rest conds)
  `(defun ,rule (,rule)
     (case-match ,rule (,before ,(mk-rule-body after conds)))))

;; expression evaluation
(defmacro assert-preserves (stepfun &rest hints)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name stepfun) "-PRESERVES") stepfun)
    (implies (and (cfgp before) (,stepfun before))
	     (cfgp (,stepfun before)))
    ,@hints))

(defrule eval-+  ((('+ i1 i2) . rest) . env) `((,(+ i1 i2) . ,rest) . ,env) (integerp i1) (integerp i2))
(defrule eval-var ((v . rest) . env) `((,x . ,rest) . ,env) (let-assoc x v env))
(defrule eval-incvar ((('++ v) . rest) . env) `((,(+ x 1) . ,rest) . ,(put-assoc-eql v (+ x 1) env))
  (let-assoc x v env))

(assert-preserves eval-+)
(assert-preserves eval-var)
(assert-preserves eval-incvar)

;; expression heating and cooling rules
(defrule heatl-+ ((('+ e1 e2) . rest) . env) `((,e1 (HOLE-+ ,e2) . ,rest) . ,env))
(defrule heatr-+ ((('+ e1 e2) . rest) . env) `((,e2 (+-HOLE ,e1) . ,rest) . ,env))
(defrule cooll-+ ((e1 ('HOLE-+ e2) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env)  (expp e1))
(defrule coolr-+ ((e2 ('+-HOLE e1) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env)  (expp e2))

(assert-preserves heatl-+)
(assert-preserves heatr-+)
(assert-preserves cooll-+)
(assert-preserves coolr-+)

;; stmt evaluation
(defrule eval-while
  ((('while e stmts) . rest) . env)
  `(((if ,e (block ,stmts (while ,e ,stmts)) (block)) . ,rest) . ,env))
(defrule eval-if
  ((('if i block1 block2) . rest) . env)
  (if (eql i 0)
      `((,block2 . ,rest) . ,env)
      `((,block1 . ,rest) . ,env))
  (integerp i))
(defrule eval-assign
  ((('assign v i) . rest) . env)
  `(,rest . ,(put-assoc-eql v i env))
  (symbolp v) (integerp i) (assoc v env))
(defrule eval-block
  ((('block . stmts) . rest) . env)
  `((,@stmts . ,rest) . ,env))
(defrule eval-eval
  ((('eval i) . rest) . env)
  `(,rest . ,env)
  (integerp i))

(assert-preserves eval-while)
(assert-preserves eval-if)
(assert-preserves eval-assign)
(defthm append-stmts-klist
  (implies (and (stmtlistp stmts) (klistp klist))
	   (klistp (append stmts klist))))
(assert-preserves eval-block)
(assert-preserves eval-eval)

;; stmt heating and cooling
(defrule heat-if
  ((('if e block1 block2) . rest) . env)
  `((,e (if-HOLE ,block1 ,block2) . ,rest) . ,env))
(defrule cool-if
  ((e ('if-HOLE block1 block2) . rest) . env)
  `(((if ,e ,block1 ,block2) . ,rest) . ,env)
  (expp e))
(defrule heat-assign
  ((('assign v e) . rest) . env)
  `((,e (assign-HOLE ,v) . ,rest) . ,env))
(defrule cool-assign
  ((e ('assign-HOLE v) . rest) . env)
  `(((assign ,v ,e) . ,rest) . ,env)
  (expp e))
(defrule heat-eval
  ((('eval e) . rest) . env)
  `((,e eval-HOLE . ,rest) . ,env))
(defrule cool-eval
  ((e 'eval-HOLE . rest) . env)
  `(((eval ,e) . ,rest) . ,env)
  (expp e))

(assert-preserves heat-if)
(assert-preserves cool-if)
(assert-preserves heat-assign)
(assert-preserves cool-assign)
(assert-preserves heat-eval)
(assert-preserves cool-eval)

(defun stepped (kbefore kafter)
  (and kbefore kafter
       (or 
	(equal kafter (eval-+ kbefore))
	(equal kafter (eval-var kbefore))
	(equal kafter (eval-incvar kbefore))
	(equal kafter (heatl-+ kbefore))
	(equal kafter (heatr-+ kbefore))
	(equal kafter (cooll-+ kbefore))
	(equal kafter (coolr-+ kbefore))
	(equal kafter (eval-while kbefore))
	(equal kafter (eval-if kbefore))
	(equal kafter (eval-assign kbefore))
	(equal kafter (eval-block kbefore))
	(equal kafter (eval-eval kbefore))
	(equal kafter (heat-if kbefore))
	(equal kafter (cool-if kbefore))
	(equal kafter (heat-assign kbefore))
	(equal kafter (cool-assign kbefore))
	(equal kafter (heat-eval kbefore))
	(equal kafter (cool-eval kbefore))
	)))

(encapsulate
 ()
 (local (in-theory (disable
	 (:definition cfgp)
	 (:definition eval-+) (:definition eval-var) (:definition eval-incvar)
	 (:definition eval-while) (:definition eval-if)
	 (:definition eval-assign) (:definition eval-block) (:definition eval-eval)
		     
	 (:definition heatl-+) (:definition heatr-+)
	 (:definition cooll-+) (:definition coolr-+)

	 (:definition heat-if) (:definition heat-assign) (:definition heat-eval)
	 (:definition cool-if) (:definition cool-assign) (:definition cool-eval))))

 (defthm stepped-preserves
   (implies (and (cfgp before) (stepped before after))
	    (cfgp after))))

(defmacro assert-conservative (newfun oldfun)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name newfun) "-CONSERVATIVE") newfun)
    (implies (,newfun before) (and (,oldfun before) (equal (,newfun before) (,oldfun before))))))

(defrule guard-heatl-+ ((('+ e1 e2) . rest) . env) `((,e1 (HOLE-+ ,e2) . ,rest) . ,env) (not (isval e1)))
(defrule guard-heatr-+ ((('+ e1 e2) . rest) . env) `((,e2 (+-HOLE ,e1) . ,rest) . ,env) (isval e1) (not (isval e2)))
(defrule guard-heat-if
  ((('if e block1 block2) . rest) . env)
  `((,e (if-HOLE ,block1 ,block2) . ,rest) . ,env)
  (not (isval e)))
(defrule guard-heat-assign
  ((('assign v e) . rest) . env)
  `((,e (assign-HOLE ,v) . ,rest) . ,env)
  (not (isval e)))
(defrule guard-heat-eval
  ((('eval e) . rest) . env)
  `((,e eval-HOLE . ,rest) . ,env)
  (not (isval e)))

(assert-conservative guard-heatl-+ heatl-+)
(assert-conservative guard-heatr-+ heatr-+)
(assert-conservative guard-heat-if heat-if)
(assert-conservative guard-heat-assign heat-assign)
(assert-conservative guard-heat-eval heat-eval)

(defrule guard-cooll-+ ((e1 ('HOLE-+ e2) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env)  (isval e1))
(defrule guard-coolr-+ ((e2 ('+-HOLE e1) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env)  (isval e2))
(defrule guard-cool-if
  ((e ('if-HOLE block1 block2) . rest) . env)
  `(((if ,e ,block1 ,block2) . ,rest) . ,env)
  (isval e))
(defrule guard-cool-assign
  ((e ('assign-HOLE v) . rest) . env)
  `(((assign ,v ,e) . ,rest) . ,env)
  (isval e))
(defrule guard-cool-eval
  ((e 'eval-HOLE . rest) . env)
  `(((eval ,e) . ,rest) . ,env)
  (isval e))

(assert-conservative guard-cooll-+ cooll-+)
(assert-conservative guard-coolr-+ coolr-+)
(assert-conservative guard-cool-if cool-if)
(assert-conservative guard-cool-assign cool-assign)
(assert-conservative guard-cool-eval cool-eval)

(defun hstep (c)
  (or (eval-+ c)
      (eval-var c)
      (eval-incvar c)
      (eval-while c)
      (eval-if c)
      (eval-assign c)
      (eval-block c)
      (eval-eval c)
      (guard-heatl-+ c)
      (guard-heatr-+ c)
      (guard-cooll-+ c)
      (guard-coolr-+ c)
      (guard-heat-if c)
      (guard-cool-if c)
      (guard-heat-assign c)
      (guard-cool-assign c)
      (guard-heat-eval c)
      (guard-cool-eval c)))

(encapsulate
 ()
 (local (in-theory (disable
	 (:definition cfgp)
	 (:definition eval-+) (:definition eval-var) (:definition eval-incvar)
	 (:definition eval-while) (:definition eval-if)
	 (:definition eval-assign) (:definition eval-block) (:definition eval-eval)
		     
	 (:definition heatl-+) (:definition heatr-+)
	 (:definition cooll-+) (:definition coolr-+)

	 (:definition heat-if) (:definition heat-assign) (:definition heat-eval)
	 (:definition cool-if) (:definition cool-assign) (:definition cool-eval)

	 (:definition guard-heatl-+) (:definition guard-heatr-+)
	 (:definition guard-cooll-+) (:definition guard-coolr-+)

	 (:definition guard-heat-if) (:definition guard-heat-assign) (:definition guard-heat-eval)
	 (:definition guard-cool-if) (:definition guard-cool-assign) (:definition guard-cool-eval))))

 (defthm hstep-wf
   (implies (and (cfgp before) (hstep before))
	    (cfgp (hstep before))))

 (defthm hstep-sound
   (implies (and (cfgp cfg) (hstep cfg))
	    (stepped cfg (hstep cfg)))))

(defun steps (n cfg)
  (if (and (integerp n) (> n 0) (hstep cfg))
      (steps (- n 1) (hstep cfg))
    cfg))

;;; End of the definitions I think would be automatically generated

;; Test execution
(steps 100 '(((+ x (+ 5 y))) . ((x . 10) (y . 100))))
;==> ((115) (X . 10) (Y . 100))

(steps 1400 '(((while x (block (assign x (+ x -1))))) . ((x . 100))))
;==> (((WHILE X (BLOCK (ASSIGN X (+ X -1))))) (X . 0))

;; now try to prove a few more things

;; first, try to characterize configurations actually reached during
;; program execution, and show the tighter set is closed under step:

(defun stmtfreezerp (f)
  (case-match f
    (('if-HOLE block1 block2) (and (stmtp block1) (stmtp block2)))
    (('assign-HOLE v) (symbolp v))
    ('eval-HOLE t)
    ))
(defun expfreezerp (f)
  (case-match f
    (('+-HOLE e) (expp e))
    (('HOLE-+ e) (expp e))
    ))

(defun expctx (k)
  (or (not k)
      (and (stmtfreezerp (car k)) (stmtlistp (cdr k)))
      (and (expfreezerp (car k)) (expctx (cdr k)))))

(defun eval-klistp (k)
  (or (not k)
      (and (stmtp (car k)) (stmtlistp (cdr k)))
      (and (expp (car k)) (expctx (cdr k)))))
      
(defun eval-cfgp (k)
  (and (eval-klistp (car k)) (envp (cdr k))))

(defthm exp-stmt-disj
  (not (and (stmtp term) (expp term)))
  :rule-classes nil)

(defthm eval-cfg-exp
  (implies (and (expp e) (envp env))
	   (eval-cfgp (cons (list e) env))))
(defthm eval-cfg-stmt
  (implies (and (stmtp s) (envp env))
	   (eval-cfgp (cons (list s) env))))

(defthm append-stmts
  (implies (and (stmtlistp stmts) (stmtlistp stmts2))
	   (stmtlistp (append stmts stmts2))))

(defmacro assert-preserves-eval (stepfun &rest hints)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name stepfun) "-PRESERVES-EVAL") stepfun)
    (implies (and (eval-cfgp before) (,stepfun before))
	     (eval-cfgp (,stepfun before)))
    ,@hints))

(assert-preserves-eval eval-+)
(assert-preserves-eval eval-var)
(assert-preserves-eval eval-incvar)
(assert-preserves-eval heatl-+)
(assert-preserves-eval heatr-+)
(assert-preserves-eval cooll-+)
(assert-preserves-eval coolr-+)
(assert-preserves-eval eval-while)
(assert-preserves-eval eval-if)

(assert-preserves-eval eval-assign)
(defthm stmts-car
  (implies (and stmts (stmtlistp stmts))
	   (stmtp (car stmts))))
(defthm stmts-cdr
  (implies (stmtlistp stmts) (stmtlistp (cdr stmts))))
(assert-preserves-eval eval-block)
(assert-preserves-eval eval-eval)

(assert-preserves-eval heat-if)
(assert-preserves-eval cool-if)
(assert-preserves-eval heat-assign)
(assert-preserves-eval cool-assign)
(assert-preserves-eval heat-eval)
(assert-preserves-eval cool-eval)

(encapsulate
 ()
 (local (in-theory (disable
	 (:definition cfgp) (:definition eval-cfgp)
	 (:definition eval-+) (:definition eval-var) (:definition eval-incvar)
	 (:definition eval-while) (:definition eval-if)
	 (:definition eval-assign) (:definition eval-block) (:definition eval-eval)
		     
	 (:definition heatl-+) (:definition heatr-+)
	 (:definition cooll-+) (:definition coolr-+)

	 (:definition heat-if) (:definition heat-assign) (:definition heat-eval)
	 (:definition cool-if) (:definition cool-assign) (:definition cool-eval))))

 (defthm step-preserve-eval
   (implies (and (eval-cfgp before) (stepped before after))
	    (eval-cfgp after))))

;; second, prove a progress lemma that on this set
;; evaluation can only get prematurely stuck at
;; an lookup, assignment, or increment on a bad variable
(defun done-or-stuck (k)
  (let ((klist (car k))
	(env (cdr k)))
    (or (not klist)
	(case-match klist ((i) (integerp i)))
	(case-match klist ((v . &) (and (symbolp v) (not (assoc v env)))))
	(case-match klist ((('++ v) . &) (and (symbolp v) (not (assoc v env)))))
	(case-match klist ((('assign v i) . &) (and (symbolp v) (integerp i) (not (assoc v env))))))))

;; progress - very expensive
(defthm progress
  (implies (eval-cfgp cfg) (or (hstep cfg) (done-or-stuck cfg)))
  :rule-classes nil
  )