#lang typed/racket

;; Define data structures for the abstract syntax tree (AST)
(require typed/rackunit)

;;Value types
(define-type ValV (U CloV PrimV StrV NumV BoolV))
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env])#:transparent)
(struct PrimV ([name : Symbol] [arity : Natural])#:transparent)
(struct StrV ([val : String])#:transparent)
(struct NumV ([val : Real])#:transparent)
(struct BoolV ([val : Boolean])#:transparent)

; Define the type environment data structure
(define-type TypeEnv (Listof TypeBind))
(struct TypeBind [(name : Symbol) (val : Type)] #:transparent)

; Define the types... for types
(define-type Type (U NumT StrT BoolT FunT ArrT VoidT))
(struct NumT () #:transparent)
(struct StrT () #:transparent)
(struct BoolT () #:transparent)
(struct FunT ([arg-types : (Listof Type)] [result-type : Type]) #:transparent)
(struct ArrT () #:transparent)
(struct VoidT () #:transparent)


; Define the typed AST
(define-type ExprC (U ValC IfC LamC IdC AppC SetC RecC ArrC BegC))
(define-type ValC (U NumC StrC))
(struct NumC ([n : Real]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct IfC ([do? : ExprC] [test : ExprC] [else? : ExprC]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [arg-types : (Listof Type)]
                                       [body : ExprC])#:transparent)
(struct IdC ([id : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)] ) #:transparent)
(struct SetC ([id : Symbol] [val : ExprC]) #:transparent)
(struct RecC ([id : Symbol] [args : (Listof Symbol)] [arg-types : (Listof Type)]
                            [body : ExprC] [type : Type] [in : ExprC]) #:transparent)
(struct BegC ([args : (Listof ExprC)]) #:transparent)
(struct ArrC ([args : (Listof ExprC)]) #:transparent)


;; Define the environment data type
(define-type Env (Listof bind))
(struct bind[(name : Symbol) (val : ValV)] #:transparent)
(define mt-env empty)


;; Helper function to parse types
(define (parse-type [sexp : Sexp]) : Type
  (match sexp
    [(? symbol? (? ValidSymbol? sym))
     (case sym
       ['num (NumT)]
       ['bool (BoolT)]
       ['str (StrT)]
       ['void (VoidT)]
       ['numarray (ArrT)]
       [else (error 'parse-type (format "VVQS: Invalid type: ~a" sym))])]
    [(list arg-types ... '-> result-type)
     (FunT (parse-types (cast arg-types (Listof Sexp))) (parse-type result-type))]
    [else (error 'parse-type (format "VVQS: Invalid type: ~a" sexp))]))

;; Helper function to parse a list of types
(define (parse-types [sexps : (Listof Sexp)]) : (Listof Type)
  (map parse-type sexps))

;; updated bad ID names for VVQS8
(define badsyms
  (hash
   ':= #f
   ': #f
   '<- #f
   '-> #f
   'begin #f
   'in #f
   'makearr #f
   '= #f
   'where #f
   'if #f
   'then #f
   '=> #f))


;; ValidSymbol? checks if a symbol is valid for use in the AST
(define (ValidSymbol? [sym : Symbol]) : Boolean
  (cond
    [(hash-has-key? badsyms sym) #f]
    [else #t]))

;; Define the lookup function for environments
(define (lookup [for : Symbol] [env : Env]) : ValV
  (match env
    [(list) (error 'lookup "VVQS: name not found in environment")]
    [(cons (bind name val) rest-env)
     (if (symbol=? for name)
         val
         (lookup for rest-env))]))

;; Lookup function for the type environment
(define (t-lookup [for : Symbol] [tenv : TypeEnv]) : Type
  (match tenv
    [(list) (error 'lookup "VVQS: name not found in type environment")]
    [(cons (TypeBind name type) rest-env)
     (if (symbol=? for name)
         type
         (t-lookup for rest-env))]))

;; Implement the top-interp function
(define (top-interp [prog-sexp : Sexp])
  ;; Define the top-level environment
  (define top-env
    (list (bind '+ (PrimV '+ 2))
          (bind '- (PrimV '- 2))
          (bind '* (PrimV '* 2))
          (bind '/ (PrimV '/ 2))
          (bind '<= (PrimV '<= 2))
          (bind 'equal? (PrimV 'equal? 2))
          (bind 'true (BoolV #t))
          (bind 'false (BoolV #f))
          (bind 'error (PrimV 'error 1))))
  (define top-tenv
    (list (TypeBind '+ (FunT (list (NumT) (NumT)) (NumT)))
          (TypeBind '- (FunT (list (NumT) (NumT)) (NumT)))
          (TypeBind '* (FunT (list (NumT) (NumT)) (NumT)))
          (TypeBind '/ (FunT (list (NumT) (NumT)) (NumT)))
          (TypeBind 'num-eq? (FunT (list (NumT) (NumT)) (BoolT)))
          (TypeBind 'str-eq? (FunT (list (StrT) (StrT)) (BoolT)))
          (TypeBind 'num-eq? (FunT (list (NumT) (NumT)) (BoolT)))
          (TypeBind '<= (FunT (list (NumT) (NumT)) (BoolT)))
          (TypeBind 'substring (FunT (list (StrT) (NumT) (NumT)) (StrT)))
          (TypeBind 'arr (FunT (list (NumT) (NumT)) (ArrT)))
          (TypeBind 'aref (FunT (list (ArrT) (NumT)) (NumT)))
          (TypeBind 'aset (FunT (list (ArrT) (NumT) (NumT)) (VoidT)))
          (TypeBind 'alen (FunT (list (ArrT)) (NumT)))))
  (define AST (parse prog-sexp))
  (if (typecheck AST top-tenv)
      (print "lit")
      (print "not lit")))
;  (serialize (interp (parse prog-sexp) top-env)))

;; main VVQS parsing function
;; parse converts an S-expression into an ExprC (AST)
;; Modify the parse function according to the new ExprC definition
;; Parse an S-expression into an ExprC
(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? real? n) (NumC n)]
    [(? symbol? (? ValidSymbol? s)) (IdC s)]
    [(? string? s) (StrC s)]
    [(list (? symbol? (? ValidSymbol? id)) '<- val) (SetC id (parse val))]
    [(list body 'if test 'then then)
     (IfC (parse body) (parse test) (parse then))]
    [(list body 'where (list (list (list (? symbol? (? ValidSymbol? bindings)) ': ty) ':= exp) ...))
     (if (= (length bindings) (length (remove-duplicates bindings)))
           (AppC (LamC (cast bindings (Listof Symbol)) (parse-types (cast ty (Listof Sexp))) (parse body))
                 (map parse (cast exp (Listof Sexp))))
           (error 'parse "VVQS: Duplicate parameter names in function definition"))]
    [(list (list (list (? symbol? (? ValidSymbol? args)) ': ty) ...) '=> body)
       (if (= (length args) (length (remove-duplicates args)))
           (LamC (cast args (Listof Symbol)) (parse-types (cast ty (Listof Sexp))) (parse body))
           (error 'parse "VVQS: Duplicate parameter names in function definition"))]
    [(list 'letrec (list (? symbol? (? ValidSymbol? name))
                         (list (list (? symbol? (? ValidSymbol? ids)) ': ty) ...) ': ret-ty '=> body) 'in in)
     (RecC name (cast ids (Listof Symbol)) (parse-types (cast ty (Listof Sexp))) (parse body) (parse-type ret-ty) (parse in))]
    [(list 'begin exp ...) (BegC (map parse exp))]
    [(list 'makearr exp ...) (ArrC (map parse exp))]
    [(list e ...)
     (match e
       [(cons f r) (AppC (parse f) (map parse r))])]
    [else (error 'parse "VVQS: Invalid expression")]))


;; The type checker for VVQS8. Recursively evaluates the type of an exprC and, if successful,
;; does nothing. If an expression isn't correctly typed, it raises the appropriate error.
(define (typecheck [expr : ExprC] [tenv : TypeEnv]) : Type
  (match expr
    [(NumC n) (NumT)]
    [(StrC s) (StrT)]
    [(ArrC a) (if (equal? (length a) (length (filter NumC? a)))
                  (ArrT)
                  (error 'typecheck "VVQS: Arr must contain nums only"))]
    [(IfC do test else) (typecheck do tenv)
                        (if (BoolT? (typecheck test tenv))
                            BoolT
                            (error 'typechecker "VVQS: if-then test case must return a boolean"))
                        (typecheck else tenv)]
    [(IdC id) (t-lookup id tenv)]
    [(SetC id val) (define var-type (t-lookup id tenv))
                   (if (equal? var-type (typecheck val tenv))
                       var-type
                       (error 'typechecker "VVQS: cannot assign a val of different type to var"))]
    [(AppC lam app-args) (match lam 
                           [(LamC lam-args arg-t body)
                            (if (equal? (length lam-args) (length app-args))
                                (if (typecheck-lam-helper arg-t app-args tenv)
                                    (match (typecheck lam tenv)
                                      [(FunT argt returnt) returnt])
                                    (error 'typechecker "VVQS: incorrect arg type for function application"))
                                (error 'typechecker "VVQS: incorrect number of args in function application"))]
                           [(IdC id) (match (t-lookup id tenv)
                                       [(FunT argt returnt)
                                        (if (equal? (length argt) (length app-args))
                                            (if (typecheck-lam-helper argt app-args tenv)
                                                returnt
                                                (error 'typechecker "VVQS: incorrect arg type for function application"))
                                            (error 'typechecker "VVQS: incorrect number of args in function application"))])]
                           [_ (error 'typechecker "VVQS: cannot apply a non-function")])]
    [(LamC args arg-types body) (define ext-tenv (append (map (λ (arg arg-type)
                                               (TypeBind arg arg-type)) args arg-types) tenv))
                                (FunT arg-types (typecheck body ext-tenv))]
    [(RecC name args arg-types body type in) (define ext-tenv
                                               (append
                                                (map (λ (arg arg-type) (TypeBind arg arg-type)) args arg-types)
                                                (list (TypeBind name (FunT arg-types type)))
                                                tenv))
                                             (if (equal? (typecheck body ext-tenv) type)
                                                 (typecheck in ext-tenv)
                                                 (error 'typechecker "VVQS: recursive body function does not evaluate to provided return type"))]))


;; Helper function for the typechecker AppC case. Compares the types of the LamC params
;; with the applied args for equality and errors on any discrepency.
(define (typecheck-lam-helper [params : (Listof Type)] [args : (Listof ExprC)]
                              [tenv : TypeEnv]) : Boolean
  (match params
    [(list) #t]
    [(cons pf pr)
     (match args
       [(cons af ar)
        (if (equal? pf (typecheck af tenv))
            (typecheck-lam-helper pr ar tenv)
            #f)])]))


;;;updated interp function to handle VVQS5, supports enviorments
;(define (interp [expr : ExprC] [env : Env]) : ValV
;  (match expr
;    [(NumC n) (NumV n)]
;    [(StrC s) (StrV s)]
;    [(IfC do? test else?)
;     (define test-result (interp test env))
;     (match test-result
;       [(BoolV #t) (interp do? env)]
;       [(BoolV #f) (interp else? env)]
;       [else (error 'interp "VVQS: Test expression in if must return a boolean")])]
;    [(LamC args body) (CloV args body env)]
;    [(IdC id)
;     (lookup id env)]
;    [(AppC fun args)
;     (define func-val (interp fun env))
;     (define arg-values (map (λ (arg) (interp (cast arg ExprC) env)) args))
;     (match func-val
;       [(CloV params body closure-env)
;        (if (= (length params) (length arg-values))
;            (let ([extended-env (append (map (λ (param arg) (bind (cast param Symbol)
;                                                                  (cast arg ValV))) params arg-values) closure-env)])
;              (interp body extended-env))
;            (error 'interp (format "VVQS: Wrong number of arguments in application")))]
;       [(PrimV name arity)
;        (if (= arity (length arg-values))
;            (apply-prim func-val arg-values env)
;            (error 'interp (format "VVQS: Wrong number of arguments for primitive ~a" name)))]
;       [else (error 'interp "VVQS: Attempted to apply non-function value")])]))

;; Apply a primitive operation based on its name
(: apply-prim (PrimV (Listof ValV) Env -> ValV))
(define (apply-prim prim-val args env)
  (match prim-val
    [(PrimV name arity)
     (match name
       ['+
        (match (list (first args) (second args))
          [(list (NumV a) (NumV b)) (NumV (+ a b))]
          [else (error "VVQS: Argument must be real")])]
       ['-
        (match (list (first args) (second args))
          [(list (NumV a) (NumV b)) (NumV (- a b))]
          [else (error "VVQS: Argument must be real")])]
       ['*
        (match (list (first args) (second args))
          [(list (NumV a) (NumV b)) (NumV (* a b))]
          [else (error "VVQS: Argument must be real")])]
       ['/
        (match (list (first args) (second args))
          [(list (NumV a) (NumV b))
           (if (zero? b)
               (error "VVQS: Division by zero")
               (NumV (/ a b)))]
          [else (error "VVQS: Argument must be real")])]
       ['<=
        (match (list (first args) (second args))
          [(list (NumV a) (NumV b)) (BoolV (<= a b))]
          [else (error "VVQS: Argument must be real")])]
       ['equal?
        (if (andmap (lambda (x) (not (or (CloV? x) (PrimV? x)))) args)
            (BoolV (equal? (serialize (first args)) (serialize (second args))))
            (BoolV #f))]
       ['error (error (format "user-error ~a" (serialize (first args))))])]))


(: serialize (ValV -> String))
(define (serialize val)
  (match val
    [(CloV params body env)
     "#<procedure>"
     #;(format "<closure: params: ~a, body: ~a>" params body)] 
    [(PrimV name arity)
     "#<primop>" 
     #;(format "<primitive: ~a, arity: ~a>" name arity)] 
    [(StrV s) s]
    [(NumV n) (number->string n)]
    [(BoolV b) (if b "true" "false")]))


;;;-------------------------------TEST CASES-----------------------------------------

;; Test for number literal
(check-equal? (parse 10) (NumC 10))

;; Test for string literal
(check-equal? (parse "hello") (StrC "hello"))

;; Test for identifier
(check-equal? (parse 'x) (IdC 'x))

;; Test for assignment
(check-equal? (parse '(x <- 10)) (SetC 'x (NumC 10)))

;; Test for if-then-else
(check-equal? (parse '(x if y then z))
              (IfC (IdC 'x) (IdC 'y) (IdC 'z)))

;; Test for where clause
(check-equal? (parse '((x) where (((y : num) := (10)))))
              (AppC
               (LamC
                '(y)
                (list (NumT))
                (AppC (IdC 'x) '()))
               (list (AppC (NumC 10) '()))))

;; Test for lambda function
(check-equal? (parse '(((x : num)) => x))
              (LamC '(x) (list (NumT)) (IdC 'x)))

;; Test for recursive function
(check-equal? (parse '(letrec (f ((x : num)) : num => x) in f))
              (RecC
               'f
               '(x)
               (list (NumT))
               (IdC 'x)
               (NumT)
               (IdC 'f))
)

;; Test for begin expression
(check-equal? (parse '(begin x y z)) (BegC (list (IdC 'x) (IdC 'y) (IdC 'z))))

;; Test for array creation
(check-equal? (parse '(makearr 1 2 3)) (ArrC (list (NumC 1) (NumC 2) (NumC 3))))

;; Test for function application
(check-equal? (parse '(f x y z)) (AppC (IdC 'f) (list (IdC 'x) (IdC 'y) (IdC 'z))))


;;; parser tests
;(define concreteLam '({x y} => {+ 3 {+ x y}}))
;(check-equal? (parse concreteLam)
;              (LamC (list 'x 'y)
;                    (AppC (IdC '+) (list (NumC 3)
;                                         (AppC (IdC '+)
;                                               (list (IdC 'x) (IdC 'y)))))))
;
;(define ifTest '(("nice" if {<= x 4} else "lame") where {[x := 5]}))
;(check-equal? (parse ifTest)
;              (AppC (LamC '(x)
;                          (IfC (StrC "nice")
;                               (AppC (IdC '<=) (list (IdC 'x) (NumC 4)))
;                               (StrC "lame")))
;                    (list (NumC 5))))
;
;;; parser errors
;(check-exn #rx"expression" (λ () (parse '(if 4))))
;(check-exn #rx"Duplicate" (λ () (parse '({x x} => {+ x x}))))
;(check-exn #rx"Duplicate" (λ () (parse '({+ yer yump} where {[yer := 4] [yer := 6]}))))
;
;
;;; interp tests
;(define lamApp '(({x y} => {+ 3 {- x y}}) 1 2))
;(check-equal? (top-interp lamApp) "2")
;(check-equal? (top-interp ifTest) "lame")
;(check-equal? (top-interp '(69 if {<= 5 7} else 96)) "69")
;
;;; interp errors
;(check-exn #rx"zero" (λ () (top-interp '(/ 5 (* 5 0)))))
;(check-exn #rx"boolean" (λ () (top-interp '(1 if 2 else 3))))
;(check-exn #rx"arguments" (λ () (top-interp '{{{x y} => {+ x 1}} 1 2 3})))
;(check-exn #rx"primitive" (λ () (top-interp '(+ 1 2 3))))
;(check-exn #rx"not found" (λ () (top-interp '((+ x y) 1 2 3))))
;(check-exn #rx"non-function" (λ () (top-interp '(3))))
;
;
;(check-exn #rx"lookup" (λ () (top-interp '({+ x y} where {[x := 5]}))))
;
;;; Test cases for NumC
;(check-equal? (top-interp '42) "42")
;
;;; Test cases for StrC
;(check-equal? (top-interp "hello") "hello")
;
;;; Test cases for IfC
;(check-equal? (top-interp '(1 if true else 2)) "1")
;(check-equal? (top-interp '(1 if false else 2)) "2")
;
;;; Test cases for LamC and AppC
;(check-equal? (top-interp '(((x y) => (+ x y)) 2 3)) "5")
;(check-equal? (top-interp '(((x) => (+ x 1)) 4)) "5")
;
;;; Test cases for IdC
;(check-equal? (top-interp 'true) "true")
;(check-equal? (top-interp 'false) "false")
;;
;;; Test cases for primitive operations
;(check-equal? (top-interp '(+ 2 3)) "5")
;(check-equal? (top-interp '(- 7 3)) "4")
;(check-equal? (top-interp '(* 4 3)) "12")
;(check-equal? (top-interp '(/ 8 2)) "4")
;(check-equal? (top-interp '(<= 2 3)) "true")
;(check-equal? (top-interp '(<= 3 3)) "true")
;(check-equal? (top-interp '(<= 4 3)) "false")
;(check-equal? (top-interp '(equal? "hello" "hello")) "true")
;(check-equal? (top-interp '(equal? "hello" "world")) "false")
;
;;; Test cases for where
;(check-equal? (top-interp '((+ x y) where ((x := 2) (y := 3)))) "5")
;(check-equal? (top-interp '((+ x y) where ((x := 4) (y := (* 4 2))))) "12")
;
;
;(check-equal? (top-interp '((((f) => ((x y) => (f x y))) ((a b) => (+ a b))) 1 2)) "3")
;
;;; serializing PrimV and CloV
;(check-equal? (serialize (PrimV '+ 4)) "#<primop>")
;(check-equal? (serialize (CloV '(a b c) (IdC 'x) '())) "#<procedure>")
;;(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env])#:transparent)
;
;;; Error cases
;(check-exn exn:fail?
;  (lambda () (top-interp '(+ 2))))
;(check-exn exn:fail?
;  (lambda () (top-interp '(+ 2 3 4))))
;(check-exn exn:fail?
;  (lambda () (top-interp '((x y) => (+ x y 2) 3))))
;(check-exn exn:fail?
;  (lambda () (top-interp '((+ x y) where ((x := 2) (y := 3) (x := 4))))))
;
;(check-exn #rx"real" (λ () (top-interp '(+ true (- false (* "fail" (/ 4 "zero")))))))
;(check-exn #rx"real" (λ () (top-interp '(+ true (- false (* "fail" 4))))))
;(check-exn #rx"real" (λ () (top-interp '(+ true (- false 3)))))
;(check-exn #rx"real" (λ () (top-interp '(+ true 2))))
;(check-exn #rx"real" (λ () (top-interp '(<= true 2))))
;;(check-exn #rx"")
;
;(define test-equal-closure
;   '{equal? {{x} => {+ x 1}} {{y} => {+ y 1}}})
;
;(check-equal? (top-interp test-equal-closure) "false")
;
;(define test-wrong-args
;   '{+ 5 10 15})
;
;(check-exn #rx"VVQS: Wrong number of arguments for +" (λ () (top-interp test-wrong-args)))
;(check-exn #rx"user-error" (λ () (top-interp '(error "hi"))))