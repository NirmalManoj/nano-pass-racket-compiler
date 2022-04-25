#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require data/queue)
(require "priority_queue.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lvec-prime.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require "type-check-Cvar.rkt")
(require "multigraph.rkt")
(require "type-check-Cif.rkt")
(require "interp-Lif.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cwhile.rkt")
(require "type-check-Lvec.rkt")
(require "interp-Cvec.rkt")
(require "type-check-Cvec.rkt")
(require "type-check-Lfun.rkt")
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Our scripts
(define (convert-residual-exp e) ;; Bonus 2
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list (Var x))) (Prim '- (list (Var x)))]
    [(Prim '- (list (Prim 'read '()))) (Prim '- (list (Prim 'read '())))]
    [(Prim '+ (list (Int n) other)) (Prim '+ (list (Int n) (pe-exp other)))]
    [(Prim '+ (list other (Int n))) (Prim '+ (list (Int n) (pe-exp other)))]
    [(Prim '+ (list other1 other2)) (Prim '+ (list (pe-exp other1) (pe-exp other2)))]

    [(Prim '- (list (Int n))) (Int (fx- 0 n))]
    [(Prim '- (list (Int n) other)) (Prim '+ (list (Int n) (Prim '- (list (pe-exp other)))))]
    [(Prim '- (list other (Int n))) (Prim '+ (list (Int (fx- 0 n)) (pe-exp other)))]
    [(Prim '- (list other1 other2)) (Prim '+ (list (pe-exp other1) (Prim '- (list (pe-exp other2)))))]
    [(Prim '- (list other)) (Prim '- (list (pe-exp other)))]

    [(Let x rhs body) (Let x (pe-exp rhs) (pe-exp body))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [((Int n1) (Prim '+ (list (Int n2) exp))) (Prim '+ (list (Int (fx+ n1 n2)) exp))] ; Comment to test Bonus 1
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-sub r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx- n1 n2))]
    [(_ _) (Prim '- (list r1 r2))]))

(define (pe-exp e)
  ;(define residual_e e) ;; Uncomment to test Bonus 1
  (define residual_e (convert-residual-exp e)) ;; Comment to test Bonus 1
  (match residual_e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '- (list e1 e2)) (pe-sub (pe-exp e1) (pe-exp e2))]
    [(Let x rhs body) (Let x (pe-exp rhs) (pe-exp body))]
    [else residual_e]))

(define (pe-Lvar p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Void) (Void)]
      [(Bool b) (Bool b)]
      [(Var x)
       (Var (dict-ref env x))]
      [(Apply fun arg*)
       (Apply ((uniquify-exp env) fun) (map (uniquify-exp env) arg*))]
      [(Int n) (Int n)]
      [(If c t e) 
      (If ((uniquify-exp env) c) 
          ((uniquify-exp env) t)
          ((uniquify-exp env) e)
          )]
      [(Let x e body)
       (let*(
         [x_new (gensym x)]
         [env_new (dict-set env x x_new)]
         )
         (Let x_new ((uniquify-exp env) e) ((uniquify-exp env_new) body))
         )]
      [(HasType exp type) (HasType exp type)]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(Begin es body) (Begin (for/list ([e es]) ((uniquify-exp env) e)) ((uniquify-exp env) body))]
      [(SetBang x exp) (SetBang (dict-ref env x) ((uniquify-exp env) exp))]
      [(WhileLoop cond body) (WhileLoop ((uniquify-exp env) cond) ((uniquify-exp env) body))]
      [else (display e)]
      )))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(ProgramDefs info fn)
     (define fn-env (for/list ([f fn])
                      (match f
                        [(Def fn_label fn_arg fn_ret '() fn_exp)
                         (cons fn_label fn_label)])))
     (ProgramDefs info
                  (for/list
                      ([f fn])
                    (match f
                      [(Def fn_label fn_arg fn_ret '() fn_exp)
                       (define param-env (for/list
                                             ([arg fn_arg])
                                           (match arg
                                             [`(,x : ,T) (cons x x)])))
                       (Def fn_label fn_arg fn_ret '() ((uniquify-exp (append param-env fn-env)) fn_exp))])))]))


(define (collect-set! e)
  (match e
    ;[]
    [(Var x) (set)]
    [(Int x) (set)]
    [(Bool x) (set)]
    [(Let x rhs body) (set-union (collect-set! rhs) (collect-set! body))]
    [(SetBang var rhs) (set-union (set var) (collect-set! rhs))]
    [(If c t e) (set-union (collect-set! c) (collect-set! t) (collect-set! e))]
    [(Prim op es) (foldl (lambda (i l) (set-union l (collect-set! i))) (set) es)]
    [(Begin es body) (set-union (foldl (lambda (i l) (set-union l (collect-set! i))) (set) es) (collect-set! body))]
    [(WhileLoop cond body) (set-union (collect-set! cond) (collect-set! body))]
    [_ (set)]))

(define (uncover-get!-instr set!-vars instr)
  (match instr
    [(Void) (Void)]
    [(Var x)
     (if (set-member? set!-vars x)
         (GetBang x)
         (Var x))]
    [(Let x rhs body)
     (Let x (uncover-get!-instr set!-vars rhs)  (uncover-get!-instr set!-vars body))]
    [(If c t e)
     (If  (uncover-get!-instr set!-vars c)  (uncover-get!-instr set!-vars t)  (uncover-get!-instr set!-vars e))]
    [(Prim op es) (Prim op (map (lambda (i) (uncover-get!-instr set!-vars i)) es))]
    [(SetBang var exp) (SetBang var (uncover-get!-instr set!-vars exp))]
    [(Begin es body) (Begin (for/list ([e es]) (uncover-get!-instr set!-vars e)) (uncover-get!-instr set!-vars body))]
    [(WhileLoop cond body) (WhileLoop (uncover-get!-instr set!-vars cond) (uncover-get!-instr set!-vars body))]
    [else instr]))

(define (uncover-get! p)
  (match p
    [(Program info e)
     (define set!-vars (collect-set! e))
     (Program info (uncover-get!-instr set!-vars e))]))

(define (atom? e)
  (or (Void? e) (Var? e) (Int? e) (Bool? e))
)

(define (rco_atom e)
  (match e
    [(Void) (values Void '())]
    [(Bool b) (values (Bool b) '())]
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(If c t e)
     (define tmp_var (gensym 'if_))
     (values (Var tmp_var) `((,tmp_var . ,(If (rco_exp c) (rco_exp t) (rco_exp e)))))]
    [(Let x rhs body)
     (define rhs_exp (rco_exp rhs))
     (define-values (body_atom body_env) (rco_atom body))
     (values body_atom (append `((,x . ,rhs_exp)) body_env))]
    [(HasType e t) #:when (atom? e)
      (values e '())]
    [(HasType e t) (let-values ([(atm env) (rco_atom e)])
                    (values (Var atm) env))]
    [(Collect bytes)
      (let ([temp (gensym 'collect-bytes)])
      (values temp `((,temp . ,(Collect bytes)))))]
    [(Allocate bytes t)
      (let ([temp (gensym 'allocate-bytes)])
      (values temp `((,temp . ,(Allocate bytes t)))))]
    [(GlobalValue x)
      (let ([temp (gensym 'global-value)])
      (values temp `((,temp . ,(GlobalValue x)))))]
    [(Prim op es)
     (define tmp_var (gensym))
     (define-values (es_var es_env)
       (for/lists (e_var e_env) ([e es]) (rco_atom e)))
     (define complete_env (append* es_env))
     (define return_env (append complete_env `((,tmp_var . ,(Prim op es_var)))))
     (values (Var tmp_var) return_env)]
    [(GetBang x)
     (define tmp_var (gensym))
     (values (Var tmp_var) `((,tmp_var . ,(Var x))))]
    [(Begin es body)
     (define tmp_var (gensym 'begin_))
     (values (Var tmp_var) `((,tmp_var . ,(Begin (for/list ([e es]) (rco_exp e)) (rco_exp body)))))]
    [else (error "rco_atom unhandled case" e)]))

(define (rco_exp e)
  (define (helper_write_lets env exp)
    (cond
      [(empty? env) exp]
      [else
       (match (car env)
         [`(,key . ,value) (Let key value (helper_write_lets (cdr env) exp))])]))
  (match e
    [(Void) (Void)]
    [(Bool b) (Bool b)]
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(If (Prim 'vector-ref es) t e)
     (define-values (es_var es_env) (rco_atom (Prim 'vector-ref es)))
     (helper_write_lets es_env (If (Prim 'eq? (list es_var (Bool #t)))
         (rco_exp t) (rco_exp e)))]
    [(If c t e)
     (If (rco_exp c) (rco_exp t) (rco_exp e))]
    [(Let x rhs body)
     (Let x (rco_exp rhs) (rco_exp body))]
    [(HasType e t) (HasType (rco_exp e) t)]
    [(Collect bytes) (Collect bytes)]
    [(Allocate bytes t) (Allocate bytes t)]
    [(GlobalValue x) (GlobalValue (rco_atom x))]
    [(Prim op es)
     (define-values (es_var es_env)
       (for/lists (e_var e_env) ([e es]) (rco_atom e)))
     (define complete_env (append* es_env))
     (helper_write_lets complete_env (Prim op es_var))]
    [(Begin es body) (Begin (for/list ([e es]) (rco_exp e)) (rco_exp body))]
    [(SetBang var exp) (SetBang var (rco_exp exp))]
    [(WhileLoop cond body) (WhileLoop (rco_exp cond) (rco_exp body))]
    [(GetBang var) (Var var)]
    [else (error "rco_exp unhandled case" e)]))


;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco_exp e))]))


(define (create_block tail basic-blocks)
  (delay
    (define t (force tail))
    (match t
      [(Goto label) (Goto label)]
      [else
       (let ([label (gensym 'block)])
         ; (set! basic-blocks (cons (cons label tail) basic-blocks))
         (dict-set! basic-blocks label t)
         (Goto label))])))

(define (explicate_pred c t e basic-blocks)
  (match c
    [(Bool #t) (force (create_block t basic-blocks))]
    [(Bool #f) (force (create_block e basic-blocks))]
    [(Var x) (IfStmt (Prim 'eq? `(,(Var x) ,(Bool #t)))
                     (force (create_block t basic-blocks))
                     (force (create_block e basic-blocks)))]
    [(GlobalValue g) (IfStmt (Prim 'eq? `(,(GlobalValue g) ,(Bool #t)))
                     (force (create_block t basic-blocks))
                     (force (create_block e basic-blocks)))]
    [(Prim 'not `(,a)) (explicate_pred a e t basic-blocks)]
    [(Prim op es)
                  (IfStmt (Prim op es)
                          (force (create_block t basic-blocks))
                          (force (create_block e basic-blocks)))]
    [(Let x rhs body)
     (let ([tail (explicate_pred body t e basic-blocks)])
       (explicate_assign rhs x tail basic-blocks))]
    [(If c_ t_ e_)
     (let ([t_blk (delay (explicate_pred t_ t e basic-blocks))]
           [e_blk (delay (explicate_pred e_ t e basic-blocks))]
           )
       (explicate_pred c_ t_blk e_blk basic-blocks))]
    [(Begin es body)
     (let ([body^ (explicate_pred body t e basic-blocks)])
       (for/foldr ([cont body^]) ([e es])
             (explicate_effect e cont basic-blocks)))]
    [else (error "explicate_pred unhandled case" c)]))


;(define (explicate_effect))
(define (explicate_effect e cont basic-blocks)
  (match e
    [(If c t e)
     (let ([t_blk (create_block (delay (explicate_effect t cont basic-blocks)) basic-blocks)]
           [e_blk (create_block (delay (explicate_effect e cont basic-blocks)) basic-blocks)])
           (explicate_pred c t_blk e_blk basic-blocks))]
    [(Let x rhs body)
     (define body_exp (explicate_effect body cont basic-blocks))
     (explicate_assign rhs x body_exp basic-blocks)]
    [(Prim 'vector-set! es) (Seq (Prim 'vector-set! es) cont)]
    [(Collect bytes) (Seq (Collect bytes) cont)]
    [(WhileLoop cnd body)
     (let* ([goto-loop (gensym 'loop)]
           [while_body (force (create_block (explicate_effect body (Goto goto-loop) basic-blocks) basic-blocks))]
           [condition_body (explicate_pred cnd while_body cont basic-blocks)])
       (dict-set! basic-blocks goto-loop condition_body)
       (Goto goto-loop))]
    [(SetBang x exp) (explicate_assign exp x cont basic-blocks)]
    [(Begin es body)
     (let ([body^ (explicate_effect body cont basic-blocks)])
           (for/foldr ([cont body^]) ([e es])
             (explicate_effect e cont basic-blocks)))]
    [else cont]))
  

; explicate-tail
(define (explicate_tail e basic-blocks)
  (match e
    [(Bool b) (Return (Bool b))]
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Prim 'vector-ref es) (Return (Prim 'vector-ref es))]
    [(Prim 'vector-set! es) (Seq (Prim 'vector-set! es) (Return (Void)))]
    [(Prim 'vector-length es) (Return (Prim 'vector-length es))]
    [(GlobalValue g) (Return (GlobalValue g))]
    [(Collect bytes) (Seq (Collect bytes) (Return (Void)))]
    [(Allocate bytes t) (Return (Allocate bytes t))]
    [(If c t e)
     (let ([t_blk (create_block (delay (explicate_tail t basic-blocks)) basic-blocks)]
           [e_blk (create_block (delay (explicate_tail e basic-blocks)) basic-blocks)])
           (explicate_pred c t_blk e_blk basic-blocks))]
    [(Let x rhs body)
     (define body_exp (explicate_tail body basic-blocks))
     (explicate_assign rhs x body_exp basic-blocks)]
    [(Prim op es) (Return (Prim op es))]
    [(HasType e t) (HasType (explicate_tail e basic-blocks) t)]
    [(WhileLoop cnd body)
     (let* ([goto-loop (gensym 'loop)]
           [while_body (create_block (explicate_effect body (Goto goto-loop) basic-blocks) basic-blocks)]
           [condition_body (explicate_pred cnd while_body (Return (Void)))])
       (dict-set! basic-blocks goto-loop condition_body)
       (Goto goto-loop))]
    [(SetBang x exp) (explicate_assign x exp (Return (Void)) basic-blocks)]
    [(Begin es body)
     (let ([body^ (explicate_tail body basic-blocks)])
           (for/foldr ([cont body^]) ([e es])
             (explicate_effect e cont basic-blocks)))]
    [else (error "explicate_tail unhandled case" e)]))

;explicate-assign
(define (explicate_assign e x cont basic-blocks)
  (match e
    [(Void) (Seq (Assign (Var x) (Void)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) (force cont))]
    [(Prim 'vector-ref es) (Seq (Assign (Var x) (Prim 'vector-ref es)) cont)]
    [(Prim 'vector-set! es) (Seq (Prim 'vector-set! es) (Seq (Assign (Var x) (Void)) cont))]
    [(Prim 'vector-length es) (Seq (Assign (Var x) (Prim 'vector-length es)) cont)]
    [(GlobalValue g) (Seq (Assign (Var x) (GlobalValue g)) cont)]
    [(Collect bytes) (Seq (Collect bytes) (Seq (Assign (Var x) (Void)) cont))]
    [(Allocate bytes t) (Seq (Assign (Var x) (Allocate bytes t)) cont)]
    [(HasType e t) (Seq (Assign (Var x) (HasType e t)) cont)]
    [(If c t e)
     (let ([t_blk (delay (explicate_assign t x cont basic-blocks))]
           [e_blk (delay (explicate_assign e x cont basic-blocks))])
           (explicate_pred c t_blk e_blk basic-blocks))]
    [(Let y rhs body)
     (define x_body (explicate_assign body x cont basic-blocks))
     (explicate_assign rhs y x_body basic-blocks)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) (force cont))]
    [(Begin es body)
     (define x_body (explicate_assign body x cont basic-blocks))
     (for/foldr ([cont x_body]) ([e es])
             (explicate_effect e cont basic-blocks))]
    [else (error "explicate_assign unhandled case" e)]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body)
     (let*
         ([basic-blocks (make-hash)]
          [_ (dict-set! basic-blocks 'start (explicate_tail body basic-blocks))])
         (CProgram info (hash->list basic-blocks)) ; Labels to Block list
       )]))


(define (select_instructions_atm a)
  (match a
    [(Int i) (Imm i)]
    [(Var _) a]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [(Void) (Imm 0)]
    [(GlobalValue g) (Global g)]
    [else (error "select_instructions_atm failed : " a)]))


(define (cmp_helper a)
  (match (select_instructions_atm a)
    [(Imm a)
     (values `(,(Instr 'movq `(,(Imm a) ,(Reg 'rax)))) (Reg 'rax))]
    [_ (values '() a)]))

(define (pointer_mask t [mask 0])
    (match t
      [`(Vector) mask]
      [`(Vector (Vector . ,_)) (bitwise-ior mask 1)]
      [`(Vector ,_) mask]
      [`(Vector . ((Vector . ,_) . ,rest)) (pointer_mask `(Vector . ,rest) (arithmetic-shift (bitwise-ior mask 1) 1))]
      [`(Vector . (,t . ,rest)) (pointer_mask `(Vector . ,rest) (arithmetic-shift mask 1))]
      [else (error "Pointer Mask Error" t)]))

(define (assign_helper regi e)
  (match e
    [(Int i) (list (Instr 'movq (list (select_instructions_atm e) regi)))]
    [(Bool b) (list (Instr 'movq (list (select_instructions_atm e) regi)))]
    [(Var _) (list (Instr 'movq (list (select_instructions_atm e) regi)))]
    [(Void) (list (Instr 'movq (list (select_instructions_atm e) regi)))]
    [(GlobalValue g) (list (Instr 'movq (list (select_instructions_atm e) regi)))]
    [(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) regi)))]
    [(Prim '- (list x)) (list (Instr 'movq (list (select_instructions_atm x) regi))
                              (Instr 'negq (list regi)))]
    [(Prim '+ (list x1 x2)) (list (Instr 'movq (list (select_instructions_atm x1) regi))
                              (Instr 'addq (list (select_instructions_atm x2) regi)))]
    [(Prim '- (list x1 x2)) (list (Instr 'movq (list (select_instructions_atm x1) regi))
                              (Instr 'subq (list (select_instructions_atm x2) regi)))])
    )

(define (select_instructions_stmt stmt)
  (match stmt
    [(Assign (Var x) (Prim '+ `((Var ,x1) ,a1))) #:when (equal? x x1)
                                         (list (Instr 'addq (list (select_instructions_atm a1) (Var x))))]
    [(Assign (Var x) (Prim '+ `(,a1 (Var ,x1)))) #:when (equal? x x1)
                                         (list (Instr 'addq (list (select_instructions_atm a1) (Var x))))]
    
    [(Assign (Var x) (Prim '- `((Var ,x1) ,a1))) #:when (equal? x x1)
                                         (list (Instr 'subq (list (select_instructions_atm a1) (Var x))))]
    [(Assign (Var x) (Prim '- `(,a1 (Var ,x1)))) #:when (equal? x x1)
                                         (list (Instr 'subq (list (select_instructions_atm a1) (Var x) (Instr 'negq (list (Var x))))))]
    [(Assign (Var x) (Prim 'vector-ref `(,tup ,(Int n)))) (define loc (* 8 (add1 n)))
                                   (list (Instr 'movq `(,tup ,(Reg 'r11))) (Instr 'movq `(,(Deref 'r11 loc) ,(Var x)))
                                         )]
    [(Assign (Var x) (Prim 'vector-set! `(,tup ,(Int n) ,rhs))) (define loc (* 8 (add1 n)))
                                   (let ([rhs (select_instructions_atm rhs)])
                                   (list (Instr 'movq `(,tup ,(Reg 'r11))) (Instr 'movq `(,rhs ,(Deref 'r11 loc)))
                                         (Instr 'movq `(,(Imm 0) ,(Var x)))))]
    [(Prim 'vector-set! `(,tup ,(Int n) ,rhs)) (define loc (* 8 (add1 n)))
                                   (let ([rhs (select_instructions_atm rhs)])
                                   (list (Instr 'movq `(,tup ,(Reg 'r11))) (Instr 'movq `(,rhs ,(Deref 'r11 loc)))))]
    [(Assign (Var x) (Prim 'vector-length (list tup))) (list (Instr 'movq `(,tup ,(Reg 'r11)))
                                                      (Instr 'movq `(,(Deref 'r11 0) ,(Var x)))
                                                      (Instr 'andq `(,(Imm 63) ,(Var x)))
                                                      (Instr 'sarq `(,(Imm 1) ,(Var x))))]
    [(Assign (Var x) (Allocate len t)) (define loc (* 8 (add1 len)))
                                (let ([tag (bitwise-ior 1 (arithmetic-shift len 1) (arithmetic-shift (pointer_mask t) 7))])
                                   (list (Instr 'movq `(,(Global 'free_ptr) ,(Reg 'r11))) (Instr 'addq `(,(Imm loc) ,(Global 'free_ptr)))
                                         (Instr 'movq `(,(Imm tag) ,(Deref 'r11 0)))
                                         (Instr 'movq `(,(Reg 'r11) ,(Var x)))
                                         ))]
    [(Assign (Var x) (Collect bytes)) (list (Instr 'movq `(,(Reg 'r15) ,(Reg 'rdi))) (Instr 'movq `(,(Imm bytes) ,(Reg 'rsi))) (Callq 'collect 2)
                                         (Instr 'movq `(,(Imm 0) ,(Var x))))]
    [(Collect bytes) (list (Instr 'movq `(,(Reg 'r15) ,(Reg 'rdi))) (Instr 'movq `(,(select_instructions_atm bytes) ,(Reg 'rsi))) (Callq 'collect 2))]
    [(Assign (Var x) (Prim 'not `(,(Var x)))) `(,(Instr 'xorq `(,(Imm 1) ,(Var x))))] ; pno 75
    [(Assign (Var x) (Prim 'not `(,(Var a)))) 
      `(,(Instr 'movq `(,a ,(Var x)))
        ,(Instr 'xorq `(,(Imm 1) ,(Var x))))]
    [(Assign (Var x) (Prim 'eq? `(,a1 ,a2)))
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1))  ,(Instr 'set `(e ,(Reg 'al))) 
                 ,(Instr 'movzbq `(,(Reg 'al) ,(Var x))))))]
    [(Assign (Var x) (Prim '< `(,a1 ,a2))) 
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1))  ,(Instr 'set `(l ,(Reg 'al)))  
                 ,(Instr 'movzbq `(,(Reg 'al) ,(Var x))))))]
    [(Assign (Var x) (Prim '<= `(,a1 ,a2))) 
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1))  ,(Instr 'set `(le ,(Reg 'al)))  
                 ,(Instr 'movzbq `(,(Reg 'al) ,(Var x))))))]
    [(Assign (Var x) (Prim '> `(,a1 ,a2))) 
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1))  ,(Instr 'set `(g ,(Reg 'al)))  
                 ,(Instr 'movzbq `(,(Reg 'al) ,(Var x))))))]
    [(Assign (Var x) (Prim '>= `(,a1 ,a2))) 
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1))  ,(Instr 'set `(ge ,(Reg 'al)))  
                 ,(Instr 'movzbq `(,(Reg 'al) ,(Var x))))))]
    [(Assign (Var x) (Void)) (list (Instr 'movq (list (select_instructions_atm (Void)) (Var x))))]
    [(Assign x e) (assign_helper x e)]
    [(Prim 'read '()) (list (Callq 'read_int 1))]
    [else (error "select instructions stmt " stmt)]
    )
  )

(define (select_instructions_tail e)
  (match e
    [(Seq stmt e*) (append (select_instructions_stmt stmt) (select_instructions_tail e*))]
    [(Return (Prim 'read '())) (list (Callq 'read_int 1) (Jmp 'conclusion))]
    [(Goto l) `(,(Jmp l))]
    [(Return (Prim 'vector-ref `(,tup ,(Int n)))) (define loc (* 8 (add1 n)))
                                   (list (Instr 'movq `(,tup ,(Reg 'r11))) (Instr 'movq `(,(Deref 'r11 loc) ,(Reg 'rax)))
                                         (Jmp 'conclusion))]
    [(Return (Prim 'vector-set! `(,tup ,(Int n) ,rhs))) (define loc (* 8 (add1 n)))
                                   (let ([rhs (select_instructions_atm rhs)])
                                   (list (Instr 'movq `(,tup ,(Reg 'r11))) (Instr 'movq `(,rhs ,(Deref 'r11 loc)))
                                         (Instr 'movq `(,(Imm 0) ,(Reg 'rax))) (Jmp 'conclusion)))]
    [(Return (Prim 'vector-length (list tup))) (list (Instr 'movq `(,tup ,(Reg 'r11)))
                                                      (Instr 'movq `(,(Deref 'r11 0) ,(Reg 'rax)))
                                                      (Instr 'andq `(,(Imm 63) ,(Reg 'rax)))
                                                      (Instr 'sarq `(,(Imm 1) ,(Reg 'rax)))
                                                      (Jmp 'conclusion))]
    [(Return (Allocate len t)) (define loc (* 8 (add1 len)))
                                (let ([tag (bitwise-ior 1 (arithmetic-shift len 1) (arithmetic-shift (pointer_mask t) 7))])
                                   (list (Instr 'movq `(,(Global 'free_ptr) ,(Reg 'r11))) (Instr 'addq `(,loc ,(Global 'free_ptr)))
                                         (Instr 'movq `(,(Imm tag) ,(Deref 'r11 0)))
                                         (Instr 'movq `(,(Reg 'r11) ,(Reg 'rax)))
                                         (Jmp 'conclusion)))]
    [(Return (Collect bytes)) (list (Instr 'movq `(,(Reg 'r15) ,(Reg 'rdi))) (Instr 'movq `(,(Imm bytes) ,(Reg 'rsi))) (Callq 'collect 2)
                                         (Instr 'movq `(,(Imm 0) ,(Reg 'rax))) (Jmp 'conclusion))]
    [(IfStmt (Prim 'eq? `(,a1 ,a2)) (Goto l1) (Goto l2))
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1)) ,(JmpIf 'e l1) ,(Jmp l2))))]
    [(IfStmt (Prim '< `(,a1 ,a2))  (Goto l1) (Goto l2))
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1)) ,(JmpIf 'l l1) ,(Jmp l2))))]
    [(IfStmt (Prim '<= `(,a1 ,a2))  (Goto l1) (Goto l2))
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1)) ,(JmpIf 'le l1) ,(Jmp l2))))]
    [(IfStmt (Prim '> `(,a1 ,a2))  (Goto l1) (Goto l2))
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1)) ,(JmpIf 'g l1) ,(Jmp l2))))]
    [(IfStmt (Prim '>= `(,a1 ,a2))  (Goto l1) (Goto l2))
     (let-values ([(mov_rax a1) (cmp_helper a1)]
                  [(a2) (select_instructions_atm a2)])
       (append mov_rax
               `(,(Instr 'cmpq `(,a2 ,a1)) ,(JmpIf 'ge l1) ,(Jmp l2))))]
    [(Return x) (append (assign_helper (Reg 'rax) x) (list (Jmp 'conclusion)))]
    [else (error "select instructions tail " e)]
    ))



;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info blocks)
     (let ([blocks (for/list ([block blocks])
                    `(,(car block) . ,(Block '() (select_instructions_tail (cdr block)))))])
       (X86Program info blocks))]))

(define (get-parent-reg r)
  (match r
  [(ByteReg 'al) (Reg 'rax)]
  [(ByteReg 'ah) (Reg 'rax)]
  [(ByteReg 'bl) (Reg 'rbx)]
  [(ByteReg 'bh) (Reg 'rbx)]
  [(ByteReg 'cl) (Reg 'rcx)]
  [(ByteReg 'ch) (Reg 'rcx)]
  [(ByteReg 'dl) (Reg 'rdx)]
  [(ByteReg 'dh) (Reg 'rdx)]
  [else r]))

(define (get-loc e)
  (match e
    [(Var p) (set e)]
    [(Reg p) (set e)]
    [(ByteReg p) (set (get-parent-reg e))]
    [else (set)]))

(define caller-saved (list (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9)
                           (Reg 'r10) (Reg 'r11)))

(define callee-saved (list (Reg 'rsp) (Reg 'rbp) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))

(define arguments (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))

(define root-stack-reg (Reg 'r15))

(define (get-k-el l k)
  (cond
    [(equal? k 0) '()]
    [else (cons (car l) (get-k-el (cdr l) (- k 1)))]))

(define (get-read instr)
  (match instr
  [(Instr 'addq (list a b)) (set-union (get-loc a) (get-loc b))]
  [(Instr 'negq (list a))(set-union (get-loc a))]
  [(Instr 'xorq (list a b)) (set-union (get-loc a) (get-loc b))]
  [(Instr 'subq (list a b)) (set-union (get-loc a) (get-loc b))]
  [(Instr 'movq (list a b))(set-union (get-loc a))]
  [(Instr 'movzbq (list a b))(set-union (get-loc a))]
  [(Instr 'cmpq (list a b)) (set-union (get-loc a) (get-loc b))]
  [(Callq label arity) (list->set (get-k-el arguments arity))]
  [else (set)]))

(define (get-write instr)
  (match instr
  [(Instr 'addq (list a b)) (set-union (get-loc b))]
  [(Instr 'negq (list a))(set-union (get-loc a))]
  [(Instr 'movq (list a b))(set-union (get-loc b))]
  [(Instr 'movzbq (list a b))(set-union (get-loc b))]
  [(Instr 'subq (list a b)) (set-union (get-loc b))]
  [(Instr 'xorq (list a b)) (set-union (get-loc b))]
  [(Instr 'set (list cc b)) (set-union (get-loc b))]
  [(Callq label arity) (list->set caller-saved)]
  [else (set)]))


(define (uncover-live-instr instr l-after label->live)
  (match instr
    ['()  l-after]
    [`(,(Jmp label) . ,rest)
     (define jmp-after (dict-ref label->live label))
     (uncover-live-instr rest (cons (set-union jmp-after (car l-after)) l-after) label->live)]
    [`(,(JmpIf _ label) . ,rest)
     (define jmp-after (dict-ref label->live label))
     (uncover-live-instr rest (cons (set-union jmp-after (car l-after)) l-after) label->live)]
    [else
     (define cur-instr (car instr))
     (define instr-read (get-read cur-instr))
     (define instr-write (get-write cur-instr))
     (uncover-live-instr (cdr instr)
                         (cons
                          (set-union (set-subtract (car l-after) instr-write) instr-read)
                          l-after)
                         label->live)]))

(define (uncover-live-block blk-body label->live)
    (define reverse-blk-body (reverse blk-body))
    (uncover-live-instr reverse-blk-body (list (set)) label->live))


(define (add-edge-block body g)
  (if (empty? body) g
      (let* ([cur-label-blk (car body)])
        (match cur-label-blk
          [(cons cur-blk-label (Block info cur-blk-body))
           (for/list ([instr cur-blk-body])
             (match instr
               [(Jmp 'conclusion) (void)]
               [(JmpIf _ 'conclusion) (void)]
               [(Jmp dest-label) (add-directed-edge! g cur-blk-label dest-label)]
               [(JmpIf _ dest-label) (add-directed-edge! g cur-blk-label dest-label)]
               [else (void)]))
           (add-edge-block (cdr body) g)]))))


;; Analyze Dataflow
(define (analyze_dataflow G p_body mapping)
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (dict-set! mapping v (set))
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define blk (dict-ref p_body node))
         (define new-live-after (match blk
                                  [(Block info blk-body)
                                   (uncover-live-block blk-body mapping)]))
         (cond [(not (equal? (car new-live-after) (dict-ref mapping node)))
                (dict-set! mapping node (car new-live-after))
                (for ([v (in-neighbors G node)])
                  (enqueue! worklist v))]))
  mapping)

;; Liveliness Analysis
(define (uncover-live p)
  (match p
    [(X86Program info body)
     (define label->live (make-hash))
     (dict-set! label->live 'conclusion  (set (Reg 'rax) (Reg 'rsp)))
     (define labels (dict-keys body))
     (define g (make-multigraph '()))
     (for/list ([l labels]) (add-vertex! g l))
     (define block-graph (add-edge-block body g))
     (set! label->live (analyze_dataflow g body label->live))
     (define blk-body (for/list ([blk body])
                        (match blk
                          [(cons blk-label (Block info block-body))
                           (define blk-live-after (uncover-live-block block-body label->live))
                           (cons blk-label (Block (dict-set info 'live-after blk-live-after) block-body))])))
     (X86Program (dict-set info 'label->live label->live) blk-body)]))


;; check whether a given element is a vector
(define (Vector? v locals-types)
  (match v
    [(Var x)
     (match (dict-ref locals-types x)
       [`(Vector . ,_) #t]
       [else #f])]
    [else #f]))



(define (build-interference-instr instr-list live-list graph locals-types)
  (match instr-list
    ['() graph]
    [`(,(Instr movq (list a b)) . ,rest)
     (define current-live (car live-list))
     (when (or (isVar? a) (isReg? a)) (add-vertex! graph a))
     (when (or (isVar? b) (isReg? b)) (add-vertex! graph b))
     (for ([l current-live])
       (add-vertex! graph l)
       (when (and (not (equal? a l)) (not (equal? b l)))
           (add-edge! graph b l)))    
     (build-interference-instr (cdr instr-list) (cdr live-list) graph locals-types)]
    
    [`(,(Instr movzbq (list a b)) . ,rest)
     (define current-live (car live-list))
     (define parent_a (get-parent-reg a))
     (define parent_b (get-parent-reg b))
     (when (or (isVar? parent_a) (isReg? parent_a)) (add-vertex! graph parent_a))
     (when (or (isVar? parent_b) (isReg? parent_b)) (add-vertex! graph parent_b))
     (for ([l current-live])
       (add-vertex! graph l)
       (when (and (not (equal? parent_a l)) (not (equal? parent_b l)))
           (add-edge! graph parent_b l)))    
     (build-interference-instr (cdr instr-list) (cdr live-list) graph locals-types)]
    
    [(Callq 'collect _)
     (define current-live (car live-list))
     (define call-live-vec-list (filter (lambda (v) (Vector? v locals-types)) live-list))
     (define current-writes (get-write (car instr-list)))
     (for* ([l current-live]
            [w current-writes])
       (add-vertex! graph l)
       (when (not (equal? l w)) (add-edge! graph l w)))
     
     (for* ([v call-live-vec-list]
            [c callee-saved])
       (when (not (equal? v c)) (add-edge! graph v c)))
     (build-interference-instr (cdr instr-list) (cdr live-list) graph locals-types)]
    
    [else
     (define current-live (car live-list))
     (define current-writes (get-write (car instr-list)))
     (for* ([l current-live]
            [w current-writes])
       (add-vertex! graph l)
       (when (not (equal? l w)) (add-edge! graph l w)))
    (build-interference-instr (cdr instr-list) (cdr live-list) graph locals-types)]))


(define (build-interference-block blk locals-types)
  (match blk
    [(cons label (Block info block-body))
     (define live-after (dict-ref info 'live-after))
     (build-interference-instr block-body (cdr live-after) (undirected-graph '()) locals-types)]))


;;build-interference
(define (build-interference p)
  (match p
    [(X86Program info body)
     (define graph (undirected-graph '()))
     (define locals-types (dict-ref info 'locals-types))
     (for/list ([blk body]) (graph-union! graph (build-interference-block blk locals-types)))
     (X86Program (dict-set info 'conflicts graph) body)]))


(define (gen-init-vertex-color g)
  (define vertices (get-vertices g))
  (define color-lval-pair (foldl (lambda (v a)
           (define last-el (car a))
           (define cur-color (cdr a))             
           (match v
             [(Reg _) (define update-color (dict-set cur-color v
                                                     (if (list? (member v alloc-registers))
                                                          (index-of alloc-registers v) (- last-el 1))))
                      (if (list? (member v alloc-registers))
                          (cons last-el update-color)
                          (cons (- last-el 1) update-color))]
             [else a])) (cons 0 '()) vertices))
  (cdr color-lval-pair))

(define (gen-init-saturation g vertex-color)
  (define vertices (get-vertices g))
  (map (lambda (v)
         (define n (get-neighbors g v))
         (define sat (foldl (lambda (nv a)
                  (if (dict-has-key? vertex-color nv) (set-union (set (dict-ref vertex-color nv)) a) a))
                (set) n))
         (cons v sat))
       vertices))

(define (isReg? p)
  (match p
    [(Reg _) #t]
    [else #f]))

(define (isByteReg? p)
  (match p
    [(ByteReg _) #t]
    [else #f]))

(define (isVar? p)
  (match p
    [(Var _) #t]
    [else #f]))


(define (get-lowest-col sat val)
  (if (set-member? sat val) (get-lowest-col sat (+ val 1)) val))



(define (color-graph g vertex-color vertex-saturation)
  (define q (make-pqueue (lambda (a b) (>
                                        (set-count (dict-ref vertex-saturation a))
                                        (set-count (dict-ref vertex-saturation b))))))
  ;; push all ements in the q
  (define vertex-node (foldl
   (lambda (v accu)
   (if (isVar? v) (dict-set accu v (pqueue-push! q v)) accu))
   '()
   (get-vertices g)))

  ;; the loop
  (define (loop g col sat q)
    ;; operation on neighbors on getting color
    (define (neighbour-operation n sat cur-color)
      (if (empty? n)
          sat
          (let* ([n-sat (set-union (dict-ref sat (car n)) (set cur-color))]
                 [new-sat (dict-set sat (car n) n-sat)])
            (pqueue-decrease-key! q (dict-ref vertex-node (car n)))
            (neighbour-operation (cdr n) new-sat cur-color))))
    
    (if (equal? (pqueue-count q) 0)
        col
        (let*
            ([cur-vertex (pqueue-pop! q)]
             [cur-color (get-lowest-col (dict-ref sat cur-vertex) 0)]
             [new-sat (neighbour-operation (filter isVar? (get-neighbors g cur-vertex)) sat cur-color)])
             (loop g (dict-set col cur-vertex cur-color) new-sat q))))
    
  (loop g vertex-color vertex-saturation q))


(define alloc-registers (list (Reg 'rbx) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9)
                           (Reg 'r10) (Reg 'r12) (Reg 'r13) (Reg 'r14)))

(define (allocate-reg-imm imm var-reg-map callee-saved locals-types)
  (match imm
    [(Imm int) (Imm int)]
    [(Reg reg) (Reg reg)]
    [(ByteReg reg) (ByteReg reg)]
    [(Var x)
     (if (isReg? (dict-ref var-reg-map imm))
         (dict-ref var-reg-map imm)
         (if (not (Vector?  (Var x) locals-types))
         (Deref 'rbp (+ (* -8 (length callee-saved)) (* -8 (dict-ref var-reg-map imm))))
         (Deref 'r15 (* 8 (dict-ref var-reg-map imm)))))]
    [(Global label) (Global label)]
    [(Deref reg imm) (Deref reg imm)]))

(define (allocate-reg-instr i var/vec-reg-map callee-saved locals-types)
  (match i
    [(Instr 'set (list cc e)) (Instr 'set (list cc (allocate-reg-imm e var/vec-reg-map callee-saved locals-types)))]
    [(Instr op (list e1)) (Instr op (list (allocate-reg-imm e1 var/vec-reg-map callee-saved locals-types)))]
    [(Instr op (list e1 e2)) (Instr op (list
                                        (allocate-reg-imm e1 var/vec-reg-map callee-saved locals-types)
                                        (allocate-reg-imm e2 var/vec-reg-map callee-saved locals-types)))]
    [_ i]))

(define (get-spilled-vars var-reg-map spilled-vars spilled-vecs locals-types)
  (if (empty? var-reg-map)
      (values spilled-vars spilled-vecs)
      (match (car var-reg-map)
        [(cons var (Reg _)) (get-spilled-vars (cdr var-reg-map) spilled-vars spilled-vecs locals-types)]
        [(cons var/vec _) (if (Vector? var/vec locals-types)
                              (get-spilled-vars (cdr var-reg-map) spilled-vars (cons (car var-reg-map) spilled-vecs) locals-types)
                              (get-spilled-vars (cdr var-reg-map) (cons (car var-reg-map) spilled-vars) spilled-vecs locals-types))])))


(define (get-used-callee var-reg-map used-callee)
  (if (empty? var-reg-map)
      used-callee
      (match (car var-reg-map)
        [(cons var (Reg r)) (if (list? (member (Reg r) callee-saved))
                                (get-used-callee (cdr var-reg-map) (cons (Reg r) used-callee))
                                (get-used-callee (cdr var-reg-map) used-callee))]
        [else (get-used-callee (cdr var-reg-map) used-callee)])))


 (define (calculate_stack_frame spilled-vars used-callee)
   (- (align (* 8 (+ (length spilled-vars) (length used-callee))) 16) (* 8 (length used-callee))))

;; allocate registers
(define (allocate-registers p)
  (match p
    [(X86Program info body)
     (define g (dict-ref info 'conflicts))
     (define init-color (gen-init-vertex-color g))
     (define init-saturation (gen-init-saturation g init-color))
     (define final-colors (color-graph g init-color init-saturation))
     (define locals-types (dict-ref info 'locals-types))
     (define vertices (get-vertices g))
     (define variables (filter (lambda (v) (and (isVar? v) (not (Vector? v locals-types)))) vertices))
     (define vectors (filter (lambda (v) (Vector? v locals-types)) vertices))
     (define variable-stack-position -1)
     (define vector-stack-position -1)
     (define var-reg-map
       (map (lambda (v)
              (cond
                [(< (dict-ref final-colors v) (length alloc-registers))
                 (cons v (list-ref alloc-registers (dict-ref final-colors v)))]
                [else (set! variable-stack-position (add1 variable-stack-position))
                      (cons v variable-stack-position)])) variables))
     (define vec-reg-map
       (map (lambda (v)
              (cond
                [(< (dict-ref final-colors v) (length alloc-registers))
                 (cons v (list-ref alloc-registers (dict-ref final-colors v)))]
                [else (set! vector-stack-position (add1 vector-stack-position))
                      (cons v vector-stack-position)])) vectors))

     (define var/vec-reg-map (append var-reg-map vec-reg-map))

     (define-values (spilled-vars spilled-vecs) (get-spilled-vars var/vec-reg-map '() '() locals-types))
     
     (define used-callee (get-used-callee var/vec-reg-map '()))
     
     (define stack-space (calculate_stack_frame spilled-vars used-callee))
     (define root-stack-space (* 8 (length spilled-vecs)))
     (define blk-body (for/list ([blk body])
                        (match blk
                          [(cons label (Block bl-info bl-body))
                           (cons label (Block bl-info (for/list ([e bl-body]) (allocate-reg-instr e var/vec-reg-map callee-saved locals-types))))])))
     (X86Program
      (dict-set* info 'stack-space stack-space 'used-callee used-callee 'root-stack-space root-stack-space) blk-body)]))


(define (patch_instr  instr)
  (match instr
    [(Instr 'movq (list s s)) (list)] ;; new update to remove redundant moves
    [(Instr 'movzbq (list s s)) (list)] ;; same
    [(Instr 'movzbq (list a (Deref  reg offset))) ;; target must be a reg
     (list (Instr 'movzbq (list a (Reg 'rax)))
           (Instr 'movq (list (Reg 'rax) (Deref  reg offset))))]
    [(Instr op (list (Deref  reg1 offset1) (Deref reg2 offset2)))
         (list (Instr 'movq (list (Deref reg1 offset1) (Reg 'rax)))
               (Instr op (list (Reg 'rax) (Deref reg2 offset2))))]
    [(Instr 'compq (list a (Imm b))) ;; target must not be Imm
     (list (Instr 'movq (list (Imm b) (Reg 'rax)))
           (Instr 'compq (list a (Reg 'rax))))]
    [else (list instr)]))

(define (patch_block block)
  (match block
    [(Block info block_body)
    (Block info (append* (for/list ([instr block_body]) (patch_instr instr))))]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info body)
     (X86Program info (for/list ([blk body])
                        (match blk
                          [`(,label . ,block) (cons label (patch_block block))]
                          )
                        ))]))

(define (prelude_conclude_block blck)
  (match blck
    [(Block info block_body)
     (Block info (for/list ([instr block_body])
                            (match instr
                              [(Jmp 'main) (Jmp '_main)]
                              [else instr])))]))


;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info body)
     (define callee-saved (dict-ref info 'used-callee))
     (define push-callee-list (for/list ([r callee-saved]) (Instr 'pushq (list r))))
     (define pop-callee-list (for/list ([r callee-saved]) (Instr 'popq (list r))))
     (define zero-out-list (for/list ([r (range 0 (quotient (dict-ref info 'root-stack-space) 8))])
                             (Instr 'movq (list (Imm 0) (Deref 'r15 (* 8 r))))))
     (define main-block (list (cons 'main (Block '()
                                                (append
                                                 (list
                                                  (Instr 'pushq (list (Reg 'rbp)))
                                                  (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                                                 push-callee-list
                                                 (list
                                                  (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
                                                  (Instr 'movq (list (Imm 65536) (Reg 'rdi)))
                                                  (Instr 'movq (list (Imm 65536) (Reg 'rsi)))
                                                  (Callq 'initialize 2)
                                                  (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))
                                                  zero-out-list
                                                  (list (Instr 'addq (list (Imm (dict-ref info 'root-stack-space)) (Reg 'r15)))
                                                  (Jmp 'start)))))))
     (define conc-block (list (cons 'conclusion (Block '()
                                                       (append
                                                        (list
                                                         (Instr 'subq (list (Imm (dict-ref info 'root-stack-space)) (Reg 'r15)))
                                                         (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
                                                        pop-callee-list
                                                        (list
                                                         (Instr 'popq (list (Reg 'rbp)))
                                                         
                                                         (Retq))
                                                        )))))
     (define program (append main-block body conc-block))
     (cond
       [(equal? (system-type 'os) 'macosx)
        (X86Program info (for/list ([blk program])
          (match blk
            [`('main . ,block) (cons '_main (prelude_conclude_block block))]
            [`(,label . ,block) (cons label (prelude_conclude_block block))])))]
       [else (X86Program info program)])]))





;; Chapter 4

; Shrink


(define (shrink-exp e)
  (match e
    [(Void) (Void)]
    [(Bool b) (Bool b)]
    [(Int i) (Int i)]
    [(Var v) (Var v)]
    [(Apply fun arg*)
     (Apply (shrink-exp fun) (map shrink-exp arg*))]
    [(If c t e) (If (shrink-exp c) (shrink-exp t) (shrink-exp e))]
    [(Let x e b) (Let x (shrink-exp e) (shrink-exp b))]
    [(HasType e t) (HasType (shrink-exp e) t)]
    ;;; Primitives
    [(Prim 'and `(,e1 ,e2)) (let ([e1 (shrink-exp e1)]
                                  [e2 (shrink-exp e2)])
                                  (If e1 e2 (Bool #f)))]
    [(Prim 'or `(,e1 ,e2))  (let ([e1 (shrink-exp e1)]
                                  [e2 (shrink-exp e2)])
                                  (If e1 (Bool #t) e2))]
    [(Prim 'vector-ref `(,t ,(Int i))) (Prim 'vector-ref `(,(shrink-exp t) ,(Int i)))]
    [(Prim 'vector-set! `(,t ,(Int i) ,e)) (Prim 'vector-set! `(,(shrink-exp t) ,(Int i) ,(shrink-exp e)))]
    [(Prim op es)
       (Prim op (for/list ([ex es]) (shrink-exp ex)))]
    ;;; Primitive end
    [(Begin es body) (Begin (for/list ([e es]) (shrink-exp e)) (shrink-exp body))]
    [(WhileLoop cond body) (WhileLoop (shrink-exp cond) (shrink-exp body))]
    [(SetBang x exp) (SetBang x (shrink-exp exp))]
    [_ e]
  )
)

(define (shrink p)
  (match p
    [(ProgramDefsExp info def_list exp)
     (define main_fn (Def 'main '() 'Integer '() (shrink-exp exp)))
     (define other_fn (for/list ([fn def_list])
                            (match fn
                              [(Def fn_label fn_arg fn_ret '() fn_exp) (Def fn_label fn_arg fn_ret '() (shrink-exp fn_exp))])))
     (ProgramDefs info (append other_fn (list main_fn)))]))



; Step 1: sequence of temporary variable bindings for the initializing expressions
; Step 2: conditional call to collect
; Step 3: call to allocate
; Step 4: initialization of the tuple

(define (exp-alloc e)
   (define (helper_write_lets env exp)
    (cond
      [(empty? env) exp]
      [else
       (match (car env)
         [`(,key . ,value) (Let key value (helper_write_lets (cdr env) exp))])]))
  (match e
    [(Void) (Void)]
    [(Bool b) (Bool b)]
    [(Int i) (Int i)]
    [(Var v) (Var v)]
    [(If c t e) (If (exp-alloc c) (exp-alloc t) (exp-alloc e))]
    [(Let x e b) (Let x (exp-alloc e) (exp-alloc b))]
    [(HasType (Prim 'vector es) t)
     (let* ([len (length es)]
          [v (gensym 'return_v)]
          [x (map (lambda (i) (gensym 'i)) es)]
          [es (map exp-alloc es)]
          [bytes (+ 8 (* len 8))]
          [alloc (Allocate len t)]
          [collec (If (Prim '< `(,(Prim '+ `(,(HasType (GlobalValue 'free_ptr) 'Integer) ,(Int bytes)))
                                ,(HasType (GlobalValue 'fromspace_end) 'Integer)))
                      (Void)
                      (Collect (Int bytes)))]
          [v_exps (map (lambda (i)
                         (Prim 'vector-set! (list (Var v) (Int i) (Var (list-ref x i)))))
                       (range 0 (length x)))]
          [all_exprs (foldr (lambda (var exp a)
                              `((,var . ,exp) . ,a))
                              '()
                              (append x (list '_) (list v) (make-list len '_))
                              (append es (list collec) (list alloc) v_exps)
                              )])
          (helper_write_lets all_exprs (Var v))
     )
     ]
    ;;; Primitives
    ;;; [(Prim 'and `(,e1 ,e2)) (let ([e1 (shrink-exp e1)]
    ;;;                               [e2 (shrink-exp e2)])
    ;;;                               (If e1 e2 (Bool #f)))]
    ;;; [(Prim 'or `(,e1 ,e2))  (let ([e1 (shrink-exp e1)]
    ;;;                               [e2 (shrink-exp e2)])
    ;;;                               (If e1 (Bool #t) e2))]
    [(Prim 'vector-ref `(,t ,(Int i))) (Prim 'vector-ref `(,(exp-alloc t) ,(Int i)))]
    [(Prim 'vector-set! `(,t ,(Int i) ,e)) (Prim 'vector-set! `(,(exp-alloc t) ,(Int i) ,(exp-alloc e)))]
    [(Prim op es)
       (Prim op (for/list ([ex es]) (exp-alloc ex)))]
    [(WhileLoop cond body) (WhileLoop (exp-alloc cond) (exp-alloc body))]
    [(Begin es body) (Begin (for/list ([ex es]) (exp-alloc ex)) (exp-alloc body))]
    [(SetBang x exp) (SetBang x (exp-alloc exp))]
    ;;; Primitive end
    )
  )

(define (expose-allocation p)
  (match p
    [(Program info e) (Program info (exp-alloc e))]))


(define (reveal-functions-exp env e)
  (match e
    [(Void) (Void)]
    [(Bool b) (Bool b)]
    [(Var x)
     (if (dict-has-key? env x) (FunRef x (dict-ref env x)) (Var x))]
    [(Apply fun arg*)
     (Apply (reveal-functions-exp env fun) (map (lambda (e) (reveal-functions-exp env e)) arg*))]
    [(Int n) (Int n)]
    [(If c t e) 
     (If (reveal-functions-exp env c) 
         (reveal-functions-exp env t)
         (reveal-functions-exp env e)
         )]
    [(Let x e body)
      (Let x (reveal-functions-exp env e) (reveal-functions-exp env body))]
    [(HasType exp type) (HasType exp type)]
    [(Prim op es)
     (Prim op (for/list ([e es]) (reveal-functions-exp env e)))]
    [(Begin es body) (Begin (for/list ([e es]) (reveal-functions-exp env e)) (reveal-functions-exp env body))]
    [(SetBang x exp) (SetBang x (reveal-functions-exp env exp))]
    [(WhileLoop cond body) (WhileLoop (reveal-functions-exp env cond) (reveal-functions-exp env body))]))


(define (reveal-functions p)
  (match p
    [(ProgramDefs info fn)
     (define fn-arity (for/list ([f fn])
                      (match f
                        [(Def fn_label fn_arg fn_ret '() fn_exp)
                         (cons fn_label (length fn_arg))])))
     (ProgramDefs info
                  (for/list
                      ([f fn])
                    (match f
                      [(Def fn_label fn_arg fn_ret '() fn_exp)
                       (Def fn_label fn_arg fn_ret '() (reveal-functions-exp fn-arity fn_exp))])))]))



;;; (define max_arg_lim 6)

;;; (define (limit-def args))

;;; (define (limit-functions p)
;;;   (match p
;;;     [(ProgramDefs info fn)
;;;      (define limit-def-body (for/list ([f fn])
;;;                       (match f
;;;                         [(Def fn_label fn_arg fn_ret '() fn_exp)
;;;                          (if (> (length fn_arg) max_arg_lim)
;;;                              (Def fn_label (limit-def fn_arg) fn_ret '() (limit-body fn_exp fn_args))
;;;                              f)])))

;;;      (ProgramDefs info
;;;                   (for/list
;;;                       ([f fn])
;;;                     (match f
;;;                       [(Def fn_label fn_arg fn_ret '() fn_exp)
;;;                        (Def fn_label fn_arg fn_ret '() (reveal-functions-exp fn-arity fn_exp))])))]))


(define compiler-passes
  `(
    ;;;  ("pe-Lvar", pe-Lvar, interp-Lvar)
     ("shrink", shrink, interp-Lfun, type-check-Lfun)
     ("uniquify" ,uniquify , interp-Lfun-prime, type-check-Lfun)
     ("reveal functions", reveal-functions, interp-Lfun-prime, type-check-Lfun)
    ;;;  ("expose allocation", expose-allocation, interp-Lvec-prime, type-check-Lvec)
    ;;;  ("uncover-get", uncover-get!, interp-Lvec-prime)
    ;;;  ("remove complex opera*", remove-complex-opera*, interp-Lvec-prime, type-check-Lvec)
    ;;;  ("explicate control" ,explicate-control , interp-Cvec ,type-check-Cvec)
    ;;;  ("instruction selection" , select-instructions ,interp-pseudo-x86-2)
    ;;;  ("uncover live", uncover-live, interp-pseudo-x86-2)
    ;;;  ("build interference", build-interference, interp-pseudo-x86-2)
    ;;;  ("allocate registers", allocate-registers , interp-pseudo-x86-2)
    ;;;  ("patch instructions" ,patch-instructions , interp-pseudo-x86-2)
    ;;;  ("prelude-and-conclusion" ,prelude-and-conclusion , interp-pseudo-x86-2)
     ))

