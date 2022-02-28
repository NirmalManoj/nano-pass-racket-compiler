#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require "type-check-Cvar.rkt")
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
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let*(
         [x_new (gensym x)]
         [env_new (dict-set env x x_new)]
         )
         (Let x_new ((uniquify-exp env) e) ((uniquify-exp env_new) body))
         )]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (rco_atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Let x rhs body)
     (define rhs_exp (rco_exp rhs))
     (define-values (body_atom body_env) (rco_atom body))
     (values body_atom (append `((,x . ,rhs_exp)) body_env))]
    [(Prim op es)
     (define tmp_var (gensym))
     (define-values (es_var es_env)
       (for/lists (e_var e_env) ([e es]) (rco_atom e)))
     (define complete_env (append* es_env))
     (define return_env (append complete_env `((,tmp_var . ,(Prim op es_var)))))
     (values (Var tmp_var) return_env)]
    [else (error "rco_atom unhandled case" e)]))

(define (rco_exp e)
  (define (helper_write_lets env exp)
    (cond
      [(empty? env) exp]
      [else
       (match (car env)
         [`(,key . ,value) (Let key value (helper_write_lets (cdr env) exp))])]))
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x rhs body)
     (Let x (rco_exp rhs) (rco_exp body))]
    [(Prim op es)
     (define-values (es_var es_env)
       (for/lists (e_var e_env) ([e es]) (rco_atom e)))
     (define complete_env (append* es_env))
     (helper_write_lets complete_env (Prim op es_var))]
    [else (error "rco_exp unhandled case" e)]))


;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco_exp e))]))

(define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body)
     (define body_exp (explicate_tail body))
     (explicate_assign rhs x body_exp)]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body)
     (define x_body (explicate_assign body x cont))
     (explicate_assign rhs y x_body)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "explicate_assign unhandled case" e)]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body) (type-check-Cvar (CProgram info `((start . ,(explicate_tail body)))))]))


(define (select_instructions_atm a)
  (match a
    [(Int i) (Imm i)]
    [(Var _) a]))

(define (assign_helper regi e)
  (match e
    [(Int i) (list (Instr 'movq (list (select_instructions_atm e) regi)))]
    [(Var _) (list (Instr 'movq (list (select_instructions_atm e) regi)))]
    [(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) regi)))]
    [(Prim '- (list x)) (list (Instr 'movq (list (select_instructions_atm x) regi))
                              (Instr 'negq (list regi)))]
    [(Prim '+ (list x1 x2)) (list (Instr 'movq (list (select_instructions_atm x1) regi))
                              (Instr 'addq (list (select_instructions_atm x2) regi)))]
    )
  )

(define (select_instructions_stmt stmt)
  (match stmt
    [(Assign (Var x) (Prim '+ `((Var ,x1) ,a1))) #:when (equal? x x1)
                                         (list (Instr 'addq (list (select_instructions_atm a1) (Var x))))]
    [(Assign (Var x) (Prim '+ `(,a1 (Var ,x1)))) #:when (equal? x x1)
                                         (list (Instr 'addq (list (select_instructions_atm a1) (Var x))))]
    [(Assign x e) (assign_helper x e)]
    )
  )

(define (select_instructions_tail e)
  (match e
    [(Seq stmt e*) (append (select_instructions_stmt stmt) (select_instructions_tail e*))]
    [(Return (Prim 'read '())) (list (Callq 'read_int 1) (Jmp 'conclusion))]
    [(Return x) (append (assign_helper (Reg 'rax) x) (list (Jmp 'conclusion)))]
    )
  )



;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info `((start . ,block))) (X86Program info (list (cons 'start (Block '() (select_instructions_tail block)))))]))


(define (calculate_stack_frame ls)
  (cond
    [(eq? (remainder (length ls) 16) 0) (* 8 (length ls))]
    [else (* 8 (+ (length ls) 1))]
    )
  )

(define (f_i v ls)
  (cond
   [(eq? (length ls) 0) 0] 
   [(eq? v (car (car ls))) 1]
   [else (+ 1 (f_i v (cdr ls)))]
   )
  )


(define (assign_homes_imm imm ls)
  (match imm
    [(Imm int) (Imm int)]
    [(Reg reg) (Reg reg)]
    [(Var x) (Deref 'rbp (* -8 (f_i x ls)))]
    )
  )

(define (assign_homes_instr i ls)
  (match i
    [(Instr op (list e1)) (Instr op (list (assign_homes_imm e1 ls)))]
    [(Instr op (list e1 e2)) (Instr op (list (assign_homes_imm e1 ls) (assign_homes_imm e2 ls)))]
    [_ i]
    )
  )

(define (assign_homes_block b ls)
  (match b
    [(Block info es) (Block info (for/list ([e es]) (assign_homes_instr e ls)))]
    )
  )

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info body)
    ; (Assign info (dict-set info 'locals-types '()))
     (X86Program (dict-set info 'stack-space (calculate_stack_frame (dict-ref info 'locals-types)))
     (for/list ([blk body])
       (match blk
         [`(,label . ,block) (cons label (assign_homes_block block  (dict-ref info 'locals-types)))]
         ))
     )
     ]
  )
  )

(define (patch_instr  instr)
  (match instr
    [(Instr op (list (Deref  reg1 offset1) (Deref reg2 offset2)))
         (list (Instr 'movq (list (Deref reg1 offset1) (Reg 'rax)))
               (Instr op (list (Reg 'rax) (Deref reg2 offset2))))]
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
     (define main-block (list (cons 'main (Block '()
                                                (list
                                                 (Instr 'pushq (list (Reg 'rbp)))
                                                 (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                                                 (Instr 'subq (list (Imm 16) (Reg 'rsp)))
                                                 (Jmp 'start))))))
     (define conc-block (list (cons 'conclusion (Block '()
                                                (list
                                                 (Instr 'addq (list (Imm 16) (Reg 'rsp)))
                                                 (Instr 'popq (list (Reg 'rbp))) 
                                                 (Retq))))))
     (define program (append main-block body conc-block))
     (cond
       [(equal? (system-type 'os) 'macosx)
        (X86Program info (for/list ([blk program])
          (match blk
            [`('main . ,block) (cons '_main (prelude_conclude_block block))]
            [`(,label . ,block) (cons label (prelude_conclude_block block))])))]
       [else (X86Program info program)])]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ("pe-Lvar", pe-Lvar, interp-Lvar)
     ("uniquify" ,uniquify ,interp-Lvar)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

