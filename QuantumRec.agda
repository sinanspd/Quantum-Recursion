module QuantumRec where

open import Agda.Primitive using (Level; lzero)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≟_)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Vec using (Vec; []; _∷_; map; lookup; updateAt)
open import Data.Fin using (Fin; _≟_)  
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Empty using (⊥; ⊥-elim)

open import Data.List as List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

module Semantics (kC kQ : ℕ) where


  ---------------- 
  -- Basic definitions
  ----------------  

  CVar : Set
  CVar = Fin kC

  QVar : Set
  QVar = Fin kQ

  ProcId : Set
  ProcId = ℕ

  UConst : Set
  UConst = ℕ

  Coeff : Set
  Coeff = ℕ

  Store : Set
  Store = Vec ℕ kC

  get : Store → CVar → ℕ
  get σ x = lookup σ x

  set : Store → CVar → ℕ → Store
  set σ x v = updateAt σ x (λ _ → v)

  getMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n
  getMany σ []       = []
  getMany σ (x ∷ xs) = get σ x ∷ getMany σ xs

  setMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n → Store
  setMany σ []       []       = σ
  setMany σ (x ∷ xs) (v ∷ vs) = setMany (set σ x v) xs vs

  data Exp : Set where
    const : ℕ → Exp
    var   : CVar → Exp
    _+e_  : Exp → Exp → Exp
    _-e_  : Exp → Exp → Exp

  evalExp : Store → Exp → ℕ
  evalExp σ (const n)  = n
  evalExp σ (var x)    = get σ x
  evalExp σ (e₁ +e e₂) = evalExp σ e₁ + evalExp σ e₂
  evalExp σ (e₁ -e e₂) = evalExp σ e₁ ∸ evalExp σ e₂

  evalMany : ∀ {n} → Store → Vec Exp n → Vec ℕ n
  evalMany σ []       = []
  evalMany σ (e ∷ es) = evalExp σ e ∷ evalMany σ es

  ----------------
  -- Boolean expressions for QC+  -- I had these in the first version, adding these back in
  ----------------

  _≤ℕ_ : ℕ → ℕ → Bool
  zero    ≤ℕ n       = true
  suc m   ≤ℕ zero    = false
  suc m   ≤ℕ suc n   = m ≤ℕ n

  _<ℕ_ : ℕ → ℕ → Bool
  m <ℕ n = suc m ≤ℕ n

  data BExp : Set where
    btrue  : BExp
    bfalse : BExp
    _==e_  : Exp → Exp → BExp
    _<e_   : Exp → Exp → BExp
    _≤e_   : Exp → Exp → BExp
    notb   : BExp → BExp
    _andb_ : BExp → BExp → BExp
    _orb_  : BExp → BExp → BExp

  evalBExp : Store → BExp → Bool
  evalBExp σ btrue          = true
  evalBExp σ bfalse         = false
  evalBExp σ (e₁ ==e e₂) with evalExp σ e₁ Data.Nat.≟ evalExp σ e₂
  ... | yes _ = true
  ... | no  _ = false
  evalBExp σ (e₁ <e e₂)     = evalExp σ e₁ <ℕ evalExp σ e₂
  evalBExp σ (e₁ ≤e e₂)     = evalExp σ e₁ ≤ℕ evalExp σ e₂
  evalBExp σ (notb b)       = not (evalBExp σ b)
  evalBExp σ (b₁ andb b₂)   = evalBExp σ b₁ ∧ evalBExp σ b₂
  evalBExp σ (b₁ orb b₂)    = evalBExp σ b₁ ∨ evalBExp σ b₂

  ----------------
  -- Basis labels (symbolic stand-in for {|ψᵢ⟩})
  ----------------

  BasisLabel : Set
  BasisLabel = ℕ

  data QState : Set where
    atom  : ℕ → QState
    aply  : ∀ {n} → UConst → Vec QVar n → QState → QState -- Vec QVar n models a register 
    split : ∀ {m d} → Vec QVar m → Vec BasisLabel d → Vec Coeff d → Vec QState d → QState

  data Cmd : Set where
    skip  : Cmd
    halt  : Cmd

    assign : ∀ {n} → Vec CVar n → Vec Exp n → Cmd
    gate   : ∀ {n} → UConst → Vec QVar n → Cmd
    seq    : Cmd → Cmd → Cmd

    ifte   : BExp → Cmd → Cmd → Cmd
    while  : BExp → Cmd → Cmd

    qif    : ∀ {m d} → Vec QVar m → Vec BasisLabel d → Vec Cmd d → Cmd

    beginLocal : ∀ {n} → Vec CVar n → Vec Exp n → Cmd → Cmd

    call0  : ProcId → Cmd
    callN  : ∀ {n} → ProcId → Vec Exp n → Cmd

  data DeclItem : Set where
    decl0 : ProcId → Cmd → DeclItem
    declN : ∀ {n} → ProcId → Vec CVar n → Cmd → DeclItem

  Decls : Set
  Decls = List DeclItem

  data HasDecl0 : ProcId → Cmd → Decls → Set where
    here0  : ∀ {P C ds} → HasDecl0 P C (decl0 P C ∷ᴸ ds)
    there0 : ∀ {P C d ds} → HasDecl0 P C ds → HasDecl0 P C (d ∷ᴸ ds)

  data HasDeclN : ∀ {n} → ProcId → Vec CVar n → Cmd → Decls → Set where
    hereN  : ∀ {n P xs C ds} → HasDeclN {n} P xs C (declN {n} P xs C ∷ᴸ ds)
    thereN : ∀ {n P xs C d ds} → HasDeclN {n} P xs C ds → HasDeclN {n} P xs C (d ∷ᴸ ds)

  find0 : (P : ProcId) → (D : Decls) → Maybe (Σ Cmd (λ C → HasDecl0 P C D))
  find0 P []ᴸ = nothing
  find0 P (decl0 P' C ∷ᴸ ds) with P Data.Nat.≟ P'
  ... | yes refl = just (C , here0)
  ... | no  _ with find0 P ds
  ...   | nothing = nothing
  ...   | just (C' , h) = just (C' , there0 h)
  find0 P (declN P' xs C ∷ᴸ ds) with find0 P ds
  ... | nothing = nothing
  ... | just (C' , h) = just (C' , there0 h)

  findN : ∀ {n} → (P : ProcId) → (D : Decls)
        → Maybe (Σ (Vec CVar n) (λ xs → Σ Cmd (λ C → HasDeclN {n} P xs C D)))
  findN {n} P []ᴸ = nothing
  findN {n} P (decl0 P' C ∷ᴸ ds) with findN {n} P ds
  ... | nothing = nothing
  ... | just (xs , (C' , h)) = just (xs , (C' , thereN h))
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) with P Data.Nat.≟ P'
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | no _ with findN {n} P ds
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | no _ | nothing = nothing
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | no _ | just (xs' , (C' , h)) = just (xs' , (C' , thereN h))
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl with n Data.Nat.≟ n'
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl | no _ with findN {n} P ds
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl | no _ | nothing = nothing
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl | no _ | just (xs' , (C' , h)) = just (xs' , (C' , thereN h))
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl | yes refl = just (xs , (C , hereN))

  record Config : Set where
    constructor ⟨_,_,_⟩
    field
      cmd : Cmd
      st  : Store
      qs  : QState
  open Config public

  natVecEq : ∀ {n} → Vec ℕ n → Vec ℕ n → Bool
  natVecEq []       []       = true
  natVecEq (x ∷ xs) (y ∷ ys) with ⌊ x Data.Nat.≟ y ⌋
  ... | true  = natVecEq xs ys
  ... | false = false

  storeEq : Store → Store → Bool
  storeEq = natVecEq

  basisEq : ∀ {d} → Vec BasisLabel d → Vec BasisLabel d → Bool
  basisEq = natVecEq

  basisEqAny : ∀ {m n} → Vec BasisLabel m → Vec BasisLabel n → Bool
  basisEqAny {m} {n} xs ys with m Data.Nat.≟ n
  ... | no _ = false
  ... | yes refl = basisEq xs ys

  qvarInVec : ∀ {n} → QVar → Vec QVar n → Bool
  qvarInVec q [] = false
  qvarInVec q (x ∷ xs) with ⌊ q Data.Fin.≟ x ⌋
  ... | true  = true
  ... | false = qvarInVec q xs

  mutual
    cmdTouches : Cmd → QVar → Bool
    cmdTouches skip q = false
    cmdTouches halt q = false
    cmdTouches (assign xs ts) q = false
    cmdTouches (gate U qs) q = qvarInVec q qs
    cmdTouches (seq C₁ C₂) q = cmdTouches C₁ q ∨ cmdTouches C₂ q
    cmdTouches (ifte b C₁ C₂) q = cmdTouches C₁ q ∨ cmdTouches C₂ q
    cmdTouches (while b C) q = cmdTouches C q
    cmdTouches (qif coin basis branches) q = qvarInVec q coin ∨ branchesTouch branches q
    cmdTouches (beginLocal xs ts C) q = cmdTouches C q
    cmdTouches (call0 P) q = false
    cmdTouches (callN P args) q = false

    branchesTouch : ∀ {d} → Vec Cmd d → QVar → Bool
    branchesTouch [] q = false
    branchesTouch (C ∷ Cs) q = cmdTouches C q ∨ branchesTouch Cs q

  externalQif : ∀ {m d} → Vec QVar m → Vec Cmd d → Bool
  externalQif [] branches = true
  externalQif (q ∷ qs) branches =
    not (branchesTouch branches q) ∧ externalQif qs branches

  -----------------
  --- Rules from the paper
  -----------------

  mutual
    data Step (D : Decls) : Config → Config → Set where
      SK : ∀ {σ ψ}
         → Step D ⟨ skip , σ , ψ ⟩ ⟨ halt , σ , ψ ⟩

      AS : ∀ {n} {xs : Vec CVar n} {ts : Vec Exp n} {σ ψ}
         → Step D ⟨ assign xs ts , σ , ψ ⟩
                  ⟨ halt , setMany σ xs (evalMany σ ts) , ψ ⟩

      GA : ∀ {n} {U : UConst} {qs : Vec QVar n} {σ ψ}
         → Step D ⟨ gate U qs , σ , ψ ⟩
                  ⟨ halt , σ , aply U qs ψ ⟩

      SC : ∀ {C₁ C₁' C₂ σ σ' ψ ψ'}
         → Step D ⟨ C₁ , σ , ψ ⟩ ⟨ C₁' , σ' , ψ' ⟩
         → Step D ⟨ seq C₁ C₂ , σ , ψ ⟩ ⟨ seq C₁' C₂ , σ' , ψ' ⟩

      SC-halt : ∀ {C₂ σ ψ}
              → Step D ⟨ seq halt C₂ , σ , ψ ⟩ ⟨ C₂ , σ , ψ ⟩

      IF-true : ∀ {b C₁ C₂ σ ψ}
              → evalBExp σ b ≡ true
              → Step D ⟨ ifte b C₁ C₂ , σ , ψ ⟩ ⟨ C₁ , σ , ψ ⟩

      IF-false : ∀ {b C₁ C₂ σ ψ}
               → evalBExp σ b ≡ false
               → Step D ⟨ ifte b C₁ C₂ , σ , ψ ⟩ ⟨ C₂ , σ , ψ ⟩

      WH : ∀ {b C σ ψ}
         → Step D ⟨ while b C , σ , ψ ⟩
                  ⟨ ifte b (seq C (while b C)) skip , σ , ψ ⟩

      BS : ∀ {n} {xs : Vec CVar n} {ts : Vec Exp n} {C σ ψ}
         → Step D ⟨ beginLocal xs ts C , σ , ψ ⟩
                  ⟨ seq (assign xs ts)
                        (seq C (assign xs (map const (getMany σ xs))))
                  , σ , ψ ⟩

      CR : ∀ {P C σ ψ}
         → HasDecl0 P C D
         → Step D ⟨ call0 P , σ , ψ ⟩ ⟨ C , σ , ψ ⟩

      RC : ∀ {n} {P : ProcId} {args : Vec Exp n} {xs : Vec CVar n} {C σ ψ}
         → HasDeclN {n} P xs C D
         → Step D ⟨ callN P args , σ , ψ ⟩
                  ⟨ beginLocal xs args C , σ , ψ ⟩

      QC : ∀ {m d}
           {coin : Vec QVar m}
           {basis : Vec BasisLabel d}
           {branches : Vec Cmd d}
           {α : Vec Coeff d}
           {θ θ' : Vec QState d}
           {σ σ' : Store}
         → externalQif coin branches ≡ true
         → BranchSteps D branches σ θ σ' θ'
         → Step D ⟨ qif coin basis branches , σ , split coin basis α θ ⟩
                  ⟨ halt , σ' , split coin basis α θ' ⟩

    data Steps (D : Decls) : Config → Config → Set where
      refl  : ∀ {x} → Steps D x x
      trans : ∀ {x y z} → Step D x y → Steps D y z → Steps D x z

    data BranchSteps (D : Decls) :
      ∀ {d} → Vec Cmd d → Store → Vec QState d → Store → Vec QState d → Set where
      bs-nil  : ∀ {σ} → BranchSteps D [] σ [] σ []
      bs-cons : ∀ {d C Cs σ σ' θ θ' θs θs'}
              → Steps D ⟨ C , σ , θ ⟩ ⟨ halt , σ' , θ' ⟩
              → BranchSteps D {d} Cs σ θs σ' θs'
              → BranchSteps D {suc d} (C ∷ Cs) σ (θ ∷ θs) σ' (θ' ∷ θs')

  steps-single : ∀ {D x y} → Step D x y → Steps D x y
  steps-single s = Steps.trans s Steps.refl

  steps-++ : ∀ {D x y z} → Steps D x y → Steps D y z → Steps D x z
  steps-++ Steps.refl          s₂ = s₂
  steps-++ (Steps.trans s s₁)  s₂ = Steps.trans s (steps-++ s₁ s₂)

  liftSeq : ∀ {D C₁ C₂ σ ψ C₁' σ' ψ'}
          → Steps D ⟨ C₁  , σ  , ψ  ⟩ ⟨ C₁' , σ' , ψ' ⟩
          → Steps D ⟨ seq C₁ C₂ , σ  , ψ  ⟩ ⟨ seq C₁' C₂ , σ' , ψ' ⟩
  liftSeq Steps.refl = Steps.refl
  liftSeq (Steps.trans s ss) = Steps.trans (SC s) (liftSeq ss)

  coinEq : ∀ {m} → Vec QVar m → Vec QVar m → Bool
  coinEq []       []       = true
  coinEq (x ∷ xs) (y ∷ ys) with ⌊ x Data.Fin.≟ y ⌋
  ... | true  = coinEq xs ys
  ... | false = false

  coinEqAny : ∀ {m n} → Vec QVar m → Vec QVar n → Bool
  coinEqAny {m} {n} xs ys with m Data.Nat.≟ n
  ... | no _ = false
  ... | yes refl = coinEq xs ys

  false≢true : false ≡ true → ⊥
  false≢true ()

  natEqBool-true : ∀ {x y : ℕ} → ⌊ x Data.Nat.≟ y ⌋ ≡ true → x ≡ y
  natEqBool-true {x} {y} eq with x Data.Nat.≟ y
  ... | yes p = p
  ... | no _  = ⊥-elim (false≢true eq)

  finEqBool-true : ∀ {n} {x y : Fin n} → ⌊ x Data.Fin.≟ y ⌋ ≡ true → x ≡ y
  finEqBool-true {x = x} {y = y} eq with x Data.Fin.≟ y
  ... | yes p = p
  ... | no _  = ⊥-elim (false≢true eq)

  natVecEq-true : ∀ {n} {xs ys : Vec ℕ n} → natVecEq xs ys ≡ true → xs ≡ ys
  natVecEq-true {xs = []} {ys = []} refl = refl
  natVecEq-true {xs = x ∷ xs} {ys = y ∷ ys} eq
    with ⌊ x Data.Nat.≟ y ⌋ in ex
  ... | false = ⊥-elim (false≢true eq)
  ... | true rewrite natEqBool-true ex | natVecEq-true {xs = xs} {ys = ys} eq = refl

  coinEq-true : ∀ {m} {xs ys : Vec QVar m} → coinEq xs ys ≡ true → xs ≡ ys
  coinEq-true {xs = []} {ys = []} refl = refl
  coinEq-true {xs = x ∷ xs} {ys = y ∷ ys} eq
    with ⌊ x Data.Fin.≟ y ⌋ in ex
  ... | false = ⊥-elim (false≢true eq)
  ... | true rewrite finEqBool-true ex | coinEq-true {xs = xs} {ys = ys} eq = refl

  basisEq-true : ∀ {d} {xs ys : Vec BasisLabel d} → basisEq xs ys ≡ true → xs ≡ ys
  basisEq-true = natVecEq-true

  storeEq-true : ∀ {σ σ' : Store} → storeEq σ σ' ≡ true → σ ≡ σ'
  storeEq-true = natVecEq-true

  ---------------- 
  -- Eval Rules 
  ----------------

  mutual
    eval : ℕ → Decls → Cmd → Store → QState → Maybe (Store × QState)
    eval zero    D C σ ψ = nothing
    eval (suc k) D skip σ ψ = just (σ , ψ)
    eval (suc k) D halt σ ψ = just (σ , ψ)

    eval (suc k) D (assign xs ts) σ ψ =
      just (setMany σ xs (evalMany σ ts) , ψ)

    eval (suc k) D (gate U qs) σ ψ =
      just (σ , aply U qs ψ)

    eval (suc k) D (seq C₁ C₂) σ ψ with eval k D C₁ σ ψ
    ... | nothing        = nothing
    ... | just (σ₁ , ψ₁) = eval k D C₂ σ₁ ψ₁

    eval (suc k) D (ifte b C₁ C₂) σ ψ =
      if evalBExp σ b
      then eval k D C₁ σ ψ
      else eval k D C₂ σ ψ

    eval (suc k) D (while b C) σ ψ =
      eval k D (ifte b (seq C (while b C)) skip) σ ψ

    eval (suc k) D (beginLocal xs ts C) σ ψ =
      eval k D (seq (assign xs ts)
                  (seq C (assign xs (map const (getMany σ xs)))))
           σ ψ

    eval (suc k) D (call0 P) σ ψ with find0 P D
    ... | nothing        = nothing
    ... | just (C , h)   = eval k D C σ ψ

    eval (suc k) D (callN {n} P args) σ ψ with findN {n} P D
    ... | nothing                  = nothing
    ... | just (xs , (C , h))      = eval k D (beginLocal xs args C) σ ψ

    eval (suc k) D (qif {m} {d} coin basis branches) σ ψ =
      evalQif k D coin basis branches σ ψ

    evalQif :
      ∀ {m d} → ℕ → Decls → Vec QVar m → Vec BasisLabel d → Vec Cmd d →
                Store → QState → Maybe (Store × QState)

    evalQif {m} {d} k D coin basis branches σ (split {m = m'} {d = d'} coin' basis' α θ)
      with m Data.Nat.≟ m' | d Data.Nat.≟ d'
    ... | no _ | _ = nothing
    ... | _ | no _ = nothing
    ... | yes refl | yes refl
        with externalQif coin branches | coinEq coin coin' | basisEq basis basis'
    ... | false | _     | _     = nothing
    ... | _     | false | _     = nothing
    ... | _     | _     | false = nothing
    ... | true  | true  | true with evalBranches k D branches σ θ
    ...   | nothing = nothing
    ...   | just (σ' , θ') = just (σ' , split coin basis α θ')

    evalQif k D coin basis branches σ ψ = nothing

    evalBranches :
      ∀ {d} → ℕ → Decls → Vec Cmd d → Store → Vec QState d
            → Maybe (Store × Vec QState d)
    evalBranches fuel D [] σ [] = just (σ , [])
    evalBranches fuel D (C ∷ Cs) σ (θ ∷ θs) with eval fuel D C σ θ
    ... | nothing = nothing
    ... | just (σ₁ , θ₁) with evalBranches fuel D Cs σ θs
    ...   | nothing = nothing
    ...   | just (σ₂ , θs') =
          if storeEq σ₁ σ₂ then just (σ₁ , θ₁ ∷ θs') else nothing

  -- postulate
  --   eval-sound-qif :
  --     ∀ {fuel D m d}
  --       {coin : Vec QVar m}
  --       {basis : Vec BasisLabel d}
  --       {branches : Vec Cmd d}
  --       {σ : Store} {ψ : QState} {σ' : Store} {ψ' : QState}
  --     → eval fuel D (qif coin basis branches) σ ψ ≡ just (σ' , ψ')
  --     → Steps D ⟨ qif coin basis branches , σ , ψ ⟩ ⟨ halt , σ' , ψ' ⟩

  mutual
    evalBranches-sound :
      ∀ {fuel D d}
        {branches : Vec Cmd d}
        {σ : Store}
        {θ : Vec QState d}
        {σ' : Store}
        {θ' : Vec QState d}
      → evalBranches fuel D branches σ θ ≡ just (σ' , θ')
      → BranchSteps D branches σ θ σ' θ'

    evalBranches-sound {branches = []} {θ = []} refl = bs-nil

    evalBranches-sound {fuel} {D} {branches = C ∷ Cs} {σ} {θ = θ ∷ θs} eq
      with eval fuel D C σ θ in eC | eq
    ... | nothing | ()
    ... | just (σ₁ , θ₁) | eq1
      with evalBranches fuel D Cs σ θs in eCs | eq1
    ...   | nothing | ()
    ...   | just (σ₂ , θs') | eq2
      with storeEq σ₁ σ₂ in es | eq2
    ...   | false | ()
    ...   | true  | refl =
          bs-cons
            (eval-sound
              {fuel = fuel} {D = D} {C = C}
              {σ = σ} {ψ = θ}
              {σ' = σ₁} {ψ' = θ₁}
              eC)
            (subst
              (λ s → BranchSteps D Cs σ θs s θs')
              (sym (storeEq-true es))
              (evalBranches-sound
                {fuel = fuel} {D = D}
                {branches = Cs}
                {σ = σ} {θ = θs}
                {σ' = σ₂} {θ' = θs'}
                eCs))
              
    eval-sound-qif :
      ∀ {fuel D m d}
        {coin : Vec QVar m}
        {basis : Vec BasisLabel d}
        {branches : Vec Cmd d}
        {σ : Store} {ψ : QState} {σ' : Store} {ψ' : QState}
      → eval fuel D (qif coin basis branches) σ ψ ≡ just (σ' , ψ')
      → Steps D ⟨ qif coin basis branches , σ , ψ ⟩ ⟨ halt , σ' , ψ' ⟩

    eval-sound-qif {fuel = zero} ()

    eval-sound-qif
      {fuel = suc k} {D} {m = m} {d = d}
      {coin} {basis} {branches} {σ} {ψ} {σ'} {ψ'} eq
      with ψ | eq
    ... | atom n | ()
    ... | aply U qs₁ ψ₀ | ()
    ... | split {m = m'} {d = d'} coin' basis' α θ | eq1
      with m Data.Nat.≟ m' | eq1
    ... | no _ | ()
    ... | yes refl | eq2
      with d Data.Nat.≟ d' | eq2
    ... | no _ | ()
    ... | yes refl | eq3
      with externalQif coin branches in ext | eq3
    ... | false | ()
    ... | true  | eq4
      with coinEq coin coin' in eco | eq4
    ... | false | ()
    ... | true  | eq5
      with basisEq basis basis' in eba | eq5
    ... | false | ()
    ... | true  | eq6
      with evalBranches k D branches σ θ in ebs | eq6
    ... | nothing | ()
    ... | just (σ₁ , θ₁) | refl =
        subst
          (λ q →
            Steps D
              ⟨ qif coin basis branches , σ , split q basis' α θ ⟩
              ⟨ halt , σ₁ , split coin basis α θ₁ ⟩)
          (coinEq-true eco)
          (subst
            (λ b →
              Steps D
                ⟨ qif coin basis branches , σ , split coin b α θ ⟩
                ⟨ halt , σ₁ , split coin basis α θ₁ ⟩)
            (basisEq-true eba)
            (steps-single
              (QC ext
                (evalBranches-sound
                  {fuel = k} {D = D}
                  {branches = branches}
                  {σ = σ} {θ = θ}
                  {σ' = σ₁} {θ' = θ₁}
                  ebs))))

    eval-sound :
      ∀ {fuel D C σ ψ σ' ψ'}
      → eval fuel D C σ ψ ≡ just (σ' , ψ')
      → Steps D ⟨ C , σ , ψ ⟩ ⟨ halt , σ' , ψ' ⟩

    eval-sound {fuel = zero} ()

    eval-sound {fuel = suc k} {C = skip} refl =
      steps-single SK

    eval-sound {fuel = suc k} {C = halt} refl =
      Steps.refl

    eval-sound {fuel = suc k} {C = assign xs ts} refl =
      steps-single AS

    eval-sound {fuel = suc k} {C = gate U qs} refl =
      steps-single GA

    -- Evaluate C₁ to completion, if it succeeds then evaluate C₂ to completion, and stitch the two together
    -- run eval-sound eq₁ to halt 
    -- liftSeq uses SC rule to lift the steps inside seq C₁ C₂, ⟨seq C₁ C₂⟩ → ⟨seq halt C₂⟩
    -- SC-halt rewrites seq halt C₂ → C₂ 
    -- eval-sound eq₂ runs C₂ to halt 
    -- steps-++ composes the two 
    eval-sound {fuel = suc k} {D} {C = seq C₁ C₂} {σ} {ψ} {σ'} {ψ'} eq
      with eval k D C₁ σ ψ in eq₁
    ... | nothing =
          impossible eq
      where
        impossible :
          nothing ≡ just (σ' , ψ') →
          Steps D ⟨ seq C₁ C₂ , σ , ψ ⟩ ⟨ halt , σ' , ψ' ⟩
        impossible ()
    ... | just (σ₁ , ψ₁)
      with eval k D C₂ σ₁ ψ₁ in eq₂
    ... | nothing =
          impossible₂ eq
      where
        impossible₂ :
          nothing ≡ just (σ' , ψ') →
          Steps D ⟨ seq C₁ C₂ , σ , ψ ⟩ ⟨ halt , σ' , ψ' ⟩
        impossible₂ ()
    ... | just (σ₂ , ψ₂)
      with eq
    ... | refl =
        steps-++
          (liftSeq (eval-sound {fuel = k} {C = C₁} eq₁))
          (Steps.trans SC-halt (eval-sound {fuel = k} {C = C₂} eq₂))

    eval-sound {fuel = suc k} {D} {C = call0 P} {σ} {ψ} {σ'} {ψ'} eq
      with find0 P D in eq₀
    ... | nothing with eq
    ...   | ()
    eval-sound {fuel = suc k} {D} {C = call0 P} {σ} {ψ} {σ'} {ψ'} eq
      | just (Cbody , h) =
        Steps.trans (CR h) (eval-sound {fuel = k} {C = Cbody} eq)

    eval-sound {fuel = suc k} {D} {C = callN {n} P args} {σ} {ψ} {σ'} {ψ'} eq
      with findN {n} P D in eq₀
    ... | nothing with eq
    ...   | ()
    eval-sound {fuel = suc k} {D} {C = callN {n} P args} {σ} {ψ} {σ'} {ψ'} eq
      | just (xs , (Cbody , h)) =
        Steps.trans (RC h) (eval-sound {fuel = k} {C = beginLocal xs args Cbody} eq)

    eval-sound {fuel = suc k} {C = qif coin basis branches} eq =
      eval-sound-qif {fuel = suc k} eq
    
    eval-sound {fuel = suc k} {D} {C = beginLocal xs ts C} {σ} {ψ} {σ'} {ψ'} eq =
      Steps.trans BS
        (eval-sound
          {fuel = k}
          {D = D}
          {C = seq (assign xs ts)
                    (seq C (assign xs (map const (getMany σ xs))))}
          {σ = σ}
          {ψ = ψ}
          {σ' = σ'}
          {ψ' = ψ'}
          eq)

    eval-sound {fuel = suc k} {D} {C = ifte b C₁ C₂} {σ} {ψ} {σ'} {ψ'} eq
      with evalBExp σ b in eb
    ... | true =
        Steps.trans (IF-true eb) (eval-sound {fuel = k} {D = D} {C = C₁} eq)
    ... | false =
        Steps.trans (IF-false eb) (eval-sound {fuel = k} {D = D} {C = C₂} eq)

    eval-sound {fuel = suc k} {D} {C = while b C} {σ} {ψ} {σ'} {ψ'} eq =
      Steps.trans WH
        (eval-sound
          {fuel = k}
          {D = D}
          {C = ifte b (seq C (while b C)) skip}
          {σ = σ}
          {ψ = ψ}
          {σ' = σ'}
          {ψ' = ψ'}
          eq)


-- EX -- Dumb example I was using the test things, this is no longer relevant now that we are embedded. I will construct a new one 
-- module Example where
--   open Semantics 2 2

--   open import Data.Fin using (zero)

--   σ0 : Store
--   σ0 = 0 ∷ 0 ∷ []

--   ψ0 : QState
--   ψ0 = atom 0

--   prog : Cmd
--   prog = seq (assign (zero ∷ []) (const 3 ∷ []))
--              (gate 0 (zero ∷ []))

--   Ds : Decls
--   Ds = []ᴸ

--   ex : eval 10 Ds prog σ0 ψ0 ≡ just (setMany σ0 (zero ∷ []) (3 ∷ []) , aply 0 ψ0)
--   ex = refl


