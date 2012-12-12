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

;; now define the relation

;;guard side conditions, make body
(defun elaborate-guards (body conds)
  (case-match conds
	      ((('let x e) . conds)
	       `(let ((,x ,e)) ,(elaborate-guards body conds)))
	      ((('let-assoc x v env) . conds)
	       `(and (symbolp ,v) (assoc ,v ,env)
		     (let ((,x (cdr (assoc ,v ,env)))) ,(elaborate-guards body conds))))
	      (nil body)
	      ((c . conds) `(and ,c ,(elaborate-guards body conds)))))

(defun mk-relation-body (conds)
  (if (consp conds)
      (cons
       `(case-match kbefore (,(caar conds) ,(elaborate-guards `(equal kafter ,(cadar conds)) (cddar conds))))
       (mk-relation-body (cdr conds)))
    nil))

(defmacro defrelation (rule &rest conds)
  `(defun ,rule (kbefore kafter)
     (or ,@(mk-relation-body conds))))

(defrelation stepped
  ;; expression evaluation
  (((('+ i1 i2) . rest) . env) `((,(+ i1 i2) . ,rest) . ,env) (integerp i1) (integerp i2))
  (((v . rest) . env) `((,x . ,rest) . ,env) (let-assoc x v env))
  (((('++ v) . rest) . env) `((,(+ x 1) . ,rest) . ,(put-assoc-eql v (+ x 1) env))
      (let-assoc x v env))

  ;; expression heating and cooling
  (((('+ e1 e2) . rest) . env) `((,e1 (HOLE-+ ,e2) . ,rest) . ,env))
  (((('+ e1 e2) . rest) . env) `((,e2 (+-HOLE ,e1) . ,rest) . ,env))
  (((e1 ('HOLE-+ e2) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env)  (expp e1))
  (((e2 ('+-HOLE e1) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env)  (expp e2))

  ;; statement evaluation
  (((('while e stmts) . rest) . env)
      `(((if ,e (block ,stmts (while ,e ,stmts)) (block)) . ,rest) . ,env))
  (((('if i block1 block2) . rest) . env)
   (if (eql i 0)
       `((,block2 . ,rest) . ,env)
       `((,block1 . ,rest) . ,env))
      (integerp i))
  (((('assign v i) . rest) . env)
     `(,rest . ,(put-assoc-eql v i env))
     (symbolp v) (integerp i) (assoc v env))
  (((('block . stmts) . rest) . env)
     `((,@stmts . ,rest) . ,env))
  (((('eval i) . rest) . env)
     `(,rest . ,env)
      (integerp i))

  ;;statement heating and cooling
  (((('if e block1 block2) . rest) . env)
   `((,e (if-HOLE ,block1 ,block2) . ,rest) . ,env))
  (((e ('if-HOLE block1 block2) . rest) . env)
   `(((if ,e ,block1 ,block2) . ,rest) . ,env)
   (expp e))
  (((('assign v e) . rest) . env)
   `((,e (assign-HOLE ,v) . ,rest) . ,env))
  (((e ('assign-HOLE v) . rest) . env)
   `(((assign ,v ,e) . ,rest) . ,env)
   (expp e))
  (((('eval e) . rest) . env)
   `((,e eval-HOLE . ,rest) . ,env))
  (((e 'eval-HOLE . rest) . env)
   `(((eval ,e) . ,rest) . ,env)
   (expp e)))

(defthm append-stmts-klist
  (implies (and (stmtlistp stmts) (klistp klist))
	   (klistp (append stmts klist))))

(defthm stepped-preserves
   (implies (and (cfgp before) (stepped before after))
	    (cfgp after)))

(defun mk-match-body (target clauses)
  (if (consp clauses)
      (cons
       `(case-match ,target (,(caar clauses) ,(elaborate-guards (cadar clauses) (cddar clauses))))
       (mk-match-body target (cdr clauses)))
    nil))

(defmacro case-match-guarded (target &rest clauses)
  `(or ,@(mk-match-body target clauses)))

(defun hstep (c)
  (case-match-guarded c
    (((('+ i1 i2) . rest) . env) `((,(+ i1 i2) . ,rest) . ,env) (integerp i1) (integerp i2))
    (((v . rest) . env) `((,x . ,rest) . ,env) (let-assoc x v env))
    (((('++ v) . rest) . env) `((,(+ x 1) . ,rest) . ,(put-assoc-eql v (+ x 1) env))
     (let-assoc x v env))

    ;; expression heating and cooling
    (((('+ e1 e2) . rest) . env) `((,e1 (HOLE-+ ,e2) . ,rest) . ,env) (not (isval e1)))
    (((('+ e1 e2) . rest) . env) `((,e2 (+-HOLE ,e1) . ,rest) . ,env) (not (isval e2)))
    (((e1 ('HOLE-+ e2) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env)  (isval e1))
    (((e2 ('+-HOLE e1) . rest) . env) `(((+ ,e1 ,e2) . ,rest) . ,env)  (isval e2))

    ;; statement evaluation
    (((('while e stmts) . rest) . env)
     `(((if ,e (block ,stmts (while ,e ,stmts)) (block)) . ,rest) . ,env))
    (((('if i block1 block2) . rest) . env)
     (if (eql i 0)
	 `((,block2 . ,rest) . ,env)
       `((,block1 . ,rest) . ,env))
     (integerp i))
    (((('assign v i) . rest) . env)
     `(,rest . ,(put-assoc-eql v i env))
     (symbolp v) (integerp i) (assoc v env))
    (((('block . stmts) . rest) . env)
     `((,@stmts . ,rest) . ,env))
    (((('eval i) . rest) . env)
     `(,rest . ,env)
     (integerp i))

    ;;statement heating and cooling
    (((('if e block1 block2) . rest) . env)
     `((,e (if-HOLE ,block1 ,block2) . ,rest) . ,env)
     (not (isval e)))
    (((e ('if-HOLE block1 block2) . rest) . env)
     `(((if ,e ,block1 ,block2) . ,rest) . ,env)
     (isval e))
    (((('assign v e) . rest) . env)
     `((,e (assign-HOLE ,v) . ,rest) . ,env)
     (not (isval e)))
    (((e ('assign-HOLE v) . rest) . env)
     `(((assign ,v ,e) . ,rest) . ,env)
     (isval e))
    (((('eval e) . rest) . env)
     `((,e eval-HOLE . ,rest) . ,env)
     (not (isval e)))
    (((e 'eval-HOLE . rest) . env)
     `(((eval ,e) . ,rest) . ,env)
     (isval e))))

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

;; first, preserve that the evaluation relation 
;; stays in this smaller space of reachable configurations
(defthm append-stmts
  (implies (and (stmtlistp stmts) (stmtlistp stmts2))
	   (stmtlistp (append stmts stmts2))))

(defthm step-preserve-eval
  (implies (and (eval-cfgp before) (stepped before after))
	   (eval-cfgp after)))

;; second, prove a progress lemma that the evaluation function
;; can take a step if we are on a well-formed configuration that
;; hasn't either finished or gotten stuck on a bad variable
(defun done-or-stuck (k)
  (let ((klist (car k))
	(env (cdr k)))
    (or (not klist)
	(case-match klist ((i) (integerp i)))
	(case-match klist ((v . &) (and (symbolp v) (not (assoc v env)))))
	(case-match klist ((('++ v) . &) (and (symbolp v) (not (assoc v env)))))
	(case-match klist ((('assign v i) . &) (and (symbolp v) (integerp i) (not (assoc v env))))))))

(defthm progress
  (implies (eval-cfgp cfg) (or (hstep cfg) (done-or-stuck cfg)))
  :rule-classes nil
  )