module proof.EndpointMLB.Core.EndpointCanonicalMLB where

-- File Charter:
--   * Executable endpoint-canonical maximal-lower-bound algorithm for GTSF
--     types.
--   * Mirrors `EndpointCanonicalMLBDesign.md` and the Python reference
--     implementation in `endpoint_canonical_mlb.py`.
--   * This module only computes endpoint-based candidates.
--   * Future work should prove this efficient profile-based algorithm
--     equivalent to the slower exhaustive algorithm in
--     `proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple`, reusing the latter's correctness
--     results for this implementation.

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Agda.Builtin.Equality using (refl)

open import Types

------------------------------------------------------------------------
-- Small boolean utilities
------------------------------------------------------------------------

infix 4 _==ᵇ_
infix 4 _<ᵇ_

_==ᵇ_ : ℕ → ℕ → Bool
zero ==ᵇ zero = true
zero ==ᵇ suc n = false
suc m ==ᵇ zero = false
suc m ==ᵇ suc n = m ==ᵇ n

_<ᵇ_ : ℕ → ℕ → Bool
zero <ᵇ zero = false
zero <ᵇ suc n = true
suc m <ᵇ zero = false
suc m <ᵇ suc n = m <ᵇ n

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

notᵇ : Bool → Bool
notᵇ true = false
notᵇ false = true

_andᵇ_ : Bool → Bool → Bool
true andᵇ b = b
false andᵇ b = false

------------------------------------------------------------------------
-- State tracked by the endpoint-canonical solver
------------------------------------------------------------------------

data Side : Set where
  leftSide : Side
  rightSide : Side

record Binder : Set where
  constructor mkBinder
  field
    binderId : ℕ
    binderSide : Side
    binderBlock : ℕ
    binderExposure : ℕ

open Binder

record Profile : Set where
  constructor mkProfile
  field
    profileId : ℕ
    profileBlock : ℕ
    profileLeft : Maybe Binder
    profileRight : Maybe Binder
    profileCreation : ℕ
    profileFirstUse : Maybe ℕ

open Profile

record Block : Set where
  constructor mkBlock
  field
    blockId : ℕ
    blockLeftBinders : List Binder
    blockRightBinders : List Binder
    blockProfiles : List Profile
    blockNextUse : ℕ

open Block

record Solver : Set where
  constructor mkSolver
  field
    nextBlock : ℕ
    nextBinder : ℕ
    nextProfile : ℕ
    nextCreation : ℕ
    blocks : List Block

open Solver

initialSolver : Solver
initialSolver = mkSolver 0 0 0 0 []

sameBinder? : Binder → Binder → Bool
sameBinder? b c = binderId b ==ᵇ binderId c

sameMaybeBinder? : Maybe Binder → Maybe Binder → Bool
sameMaybeBinder? nothing nothing = true
sameMaybeBinder? (just b) (just c) = sameBinder? b c
sameMaybeBinder? _ _ = false

lookupBlock : ℕ → List Block → Maybe Block
lookupBlock id [] = nothing
lookupBlock id (b ∷ bs) with id ==ᵇ blockId b
lookupBlock id (b ∷ bs) | true = just b
lookupBlock id (b ∷ bs) | false = lookupBlock id bs

replaceBlock : Block → List Block → List Block
replaceBlock b [] = b ∷ []
replaceBlock b (c ∷ cs) with blockId b ==ᵇ blockId c
replaceBlock b (c ∷ cs) | true = b ∷ cs
replaceBlock b (c ∷ cs) | false = c ∷ replaceBlock b cs

freshBlock : Solver → Block × Solver
freshBlock s =
  b , mkSolver (suc (nextBlock s)) (nextBinder s) (nextProfile s)
               (nextCreation s) (b ∷ blocks s)
  where
    b = mkBlock (nextBlock s) [] [] [] 0

freshBinder : Side → Block → Solver → Binder × (Block × Solver)
freshBinder leftSide b s =
  binder , (block′ , solver′)
  where
    exposure = length (blockLeftBinders b)
    binder = mkBinder (nextBinder s) leftSide (blockId b) exposure
    block′ =
      mkBlock (blockId b) (blockLeftBinders b ++ (binder ∷ []))
              (blockRightBinders b) (blockProfiles b) (blockNextUse b)
    solver′ =
      mkSolver (nextBlock s) (suc (nextBinder s)) (nextProfile s)
               (nextCreation s) (replaceBlock block′ (blocks s))
freshBinder rightSide b s =
  binder , (block′ , solver′)
  where
    exposure = length (blockRightBinders b)
    binder = mkBinder (nextBinder s) rightSide (blockId b) exposure
    block′ =
      mkBlock (blockId b) (blockLeftBinders b)
              (blockRightBinders b ++ (binder ∷ [])) (blockProfiles b)
              (blockNextUse b)
    solver′ =
      mkSolver (nextBlock s) (suc (nextBinder s)) (nextProfile s)
               (nextCreation s) (replaceBlock block′ (blocks s))

------------------------------------------------------------------------
-- Raw output before local profile placeholders are closed
------------------------------------------------------------------------

data RawVar : Set where
  rawBound : ℕ → RawVar
  rawProfile : ℕ → RawVar
  rawFree : ℕ → RawVar

data RawTy : Set where
  rawVar : RawVar → RawTy
  rawBase : Base → RawTy
  rawStar : RawTy
  rawArr : RawTy → RawTy → RawTy
  rawAll : RawTy → RawTy

data Ref : Set where
  boundRef : Binder → Ref
  freeRef : ℕ → Ref

Env : Set
Env = List Binder

lookupEnv : Env → ℕ → Ref
lookupEnv [] X = freeRef X
lookupEnv (b ∷ env) zero = boundRef b
lookupEnv (b ∷ env) (suc X) = lookupEnv env X

------------------------------------------------------------------------
-- List helpers
------------------------------------------------------------------------

filterᵇ : {A : Set} → (A → Bool) → List A → List A
filterᵇ p [] = []
filterᵇ p (x ∷ xs) with p x
filterᵇ p (x ∷ xs) | true = x ∷ filterᵇ p xs
filterᵇ p (x ∷ xs) | false = filterᵇ p xs

insertBy : {A : Set} → (A → A → Bool) → A → List A → List A
insertBy before x [] = x ∷ []
insertBy before x (y ∷ ys) with before x y
insertBy before x (y ∷ ys) | true = x ∷ y ∷ ys
insertBy before x (y ∷ ys) | false = y ∷ insertBy before x ys

sortBy : {A : Set} → (A → A → Bool) → List A → List A
sortBy before [] = []
sortBy before (x ∷ xs) = insertBy before x (sortBy before xs)

memberBinder? : Binder → List Binder → Bool
memberBinder? b [] = false
memberBinder? b (c ∷ cs) with sameBinder? b c
memberBinder? b (c ∷ cs) | true = true
memberBinder? b (c ∷ cs) | false = memberBinder? b cs

memberProfileId? : ℕ → List Profile → Bool
memberProfileId? id [] = false
memberProfileId? id (p ∷ ps) with id ==ᵇ profileId p
memberProfileId? id (p ∷ ps) | true = true
memberProfileId? id (p ∷ ps) | false = memberProfileId? id ps

removeProfile : Profile → List Profile → List Profile
removeProfile p [] = []
removeProfile p (q ∷ qs) with profileId p ==ᵇ profileId q
removeProfile p (q ∷ qs) | true = qs
removeProfile p (q ∷ qs) | false = q ∷ removeProfile p qs

------------------------------------------------------------------------
-- Profile creation and block closing
------------------------------------------------------------------------

profileBlockOf : Maybe Binder → Maybe Binder → Maybe ℕ
profileBlockOf (just l) (just r) with binderBlock l ==ᵇ binderBlock r
profileBlockOf (just l) (just r) | true = just (binderBlock l)
profileBlockOf (just l) (just r) | false = nothing
profileBlockOf (just l) nothing = just (binderBlock l)
profileBlockOf nothing (just r) = just (binderBlock r)
profileBlockOf nothing nothing = nothing

findExactProfile :
  Maybe Binder → Maybe Binder → List Profile → Maybe Profile
findExactProfile left right [] = nothing
findExactProfile left right (p ∷ ps)
    with sameMaybeBinder? left (profileLeft p)
       | sameMaybeBinder? right (profileRight p)
findExactProfile left right (p ∷ ps) | true | true = just p
findExactProfile left right (p ∷ ps) | _ | _ =
  findExactProfile left right ps

leftConflict? : Maybe Binder → Profile → Bool
leftConflict? nothing p = false
leftConflict? (just b) p with profileLeft p
leftConflict? (just b) p | nothing = false
leftConflict? (just b) p | just c = sameBinder? b c

rightConflict? : Maybe Binder → Profile → Bool
rightConflict? nothing p = false
rightConflict? (just b) p with profileRight p
rightConflict? (just b) p | nothing = false
rightConflict? (just b) p | just c = sameBinder? b c

hasConflict? : Maybe Binder → Maybe Binder → List Profile → Bool
hasConflict? left right [] = false
hasConflict? left right (p ∷ ps)
    with leftConflict? left p | rightConflict? right p
hasConflict? left right (p ∷ ps) | true | _ = true
hasConflict? left right (p ∷ ps) | false | true = true
hasConflict? left right (p ∷ ps) | false | false =
  hasConflict? left right ps

requestProfile :
  Maybe Binder → Maybe Binder → Solver → Maybe (Profile × Solver)
requestProfile left right s with profileBlockOf left right
requestProfile left right s | nothing = nothing
requestProfile left right s | just bid with lookupBlock bid (blocks s)
requestProfile left right s | just bid | nothing = nothing
requestProfile left right s | just bid | just b
    with findExactProfile left right (blockProfiles b)
requestProfile left right s | just bid | just b | just p = just (p , s)
requestProfile left right s | just bid | just b | nothing
    with hasConflict? left right (blockProfiles b)
requestProfile left right s | just bid | just b | nothing | true = nothing
requestProfile left right s | just bid | just b | nothing | false =
  just (p , solver′)
  where
    p =
      mkProfile (nextProfile s) bid left right (nextCreation s)
                (just (blockNextUse b))
    b′ =
      mkBlock (blockId b) (blockLeftBinders b) (blockRightBinders b)
              (blockProfiles b ++ (p ∷ [])) (suc (blockNextUse b))
    solver′ =
      mkSolver (nextBlock s) (nextBinder s) (suc (nextProfile s))
               (suc (nextCreation s)) (replaceBlock b′ (blocks s))

profileUsesLeft? : Binder → Profile → Bool
profileUsesLeft? b p with profileLeft p
profileUsesLeft? b p | nothing = false
profileUsesLeft? b p | just c = sameBinder? b c

profileUsesRight? : Binder → Profile → Bool
profileUsesRight? b p with profileRight p
profileUsesRight? b p | nothing = false
profileUsesRight? b p | just c = sameBinder? b c

usedLeft? : Binder → List Profile → Bool
usedLeft? b [] = false
usedLeft? b (p ∷ ps) with profileUsesLeft? b p
usedLeft? b (p ∷ ps) | true = true
usedLeft? b (p ∷ ps) | false = usedLeft? b ps

usedRight? : Binder → List Profile → Bool
usedRight? b [] = false
usedRight? b (p ∷ ps) with profileUsesRight? b p
usedRight? b (p ∷ ps) | true = true
usedRight? b (p ∷ ps) | false = usedRight? b ps

unusedLeft : Block → List Binder
unusedLeft b =
  filterᵇ (λ x → notᵇ (usedLeft? x (blockProfiles b)))
          (blockLeftBinders b)

unusedRight : Block → List Binder
unusedRight b =
  filterᵇ (λ x → notᵇ (usedRight? x (blockProfiles b)))
          (blockRightBinders b)

pairUnused :
  List Binder → List Binder → Block → Solver → Maybe (Block × Solver)
pairUnused [] [] b s = just (b , s)
pairUnused (l ∷ ls) (r ∷ rs) b s =
  pairUnused ls rs b′ solver′
  where
    p =
      mkProfile (nextProfile s) (blockId b) (just l) (just r)
                (nextCreation s) nothing
    b′ =
      mkBlock (blockId b) (blockLeftBinders b) (blockRightBinders b)
              (blockProfiles b ++ (p ∷ [])) (blockNextUse b)
    solver′ =
      mkSolver (nextBlock s) (nextBinder s) (suc (nextProfile s))
               (suc (nextCreation s)) (replaceBlock b′ (blocks s))
pairUnused [] (r ∷ rs) b s = nothing
pairUnused (l ∷ ls) [] b s = nothing

------------------------------------------------------------------------
-- Profile ordering
------------------------------------------------------------------------

data Cmp : Set where
  less : Cmp
  equal : Cmp
  greater : Cmp

cmpNat : ℕ → ℕ → Cmp
cmpNat m n with m <ᵇ n | n <ᵇ m
cmpNat m n | true | _ = less
cmpNat m n | false | true = greater
cmpNat m n | false | false = equal

cmpMaybeNat : Maybe ℕ → Maybe ℕ → Cmp
cmpMaybeNat (just m) (just n) = cmpNat m n
cmpMaybeNat (just m) nothing = less
cmpMaybeNat nothing (just n) = greater
cmpMaybeNat nothing nothing = equal

cmpMaybeBinderPresence : Maybe Binder → Maybe Binder → Cmp
cmpMaybeBinderPresence (just b) (just c) = equal
cmpMaybeBinderPresence (just b) nothing = less
cmpMaybeBinderPresence nothing (just c) = greater
cmpMaybeBinderPresence nothing nothing = equal

cmpMaybeBinderExposure : Maybe Binder → Maybe Binder → Cmp
cmpMaybeBinderExposure (just b) (just c) =
  cmpNat (binderExposure b) (binderExposure c)
cmpMaybeBinderExposure _ _ = equal

cmpToBool : Cmp → Bool
cmpToBool less = true
cmpToBool equal = false
cmpToBool greater = false

tieBefore? : Profile → Profile → Bool
tieBefore? p q with cmpMaybeNat (profileFirstUse p) (profileFirstUse q)
tieBefore? p q | less = true
tieBefore? p q | greater = false
tieBefore? p q | equal
    with cmpMaybeBinderPresence (profileLeft p) (profileLeft q)
tieBefore? p q | equal | less = true
tieBefore? p q | equal | greater = false
tieBefore? p q | equal | equal
    with cmpMaybeBinderExposure (profileLeft p) (profileLeft q)
tieBefore? p q | equal | equal | less = true
tieBefore? p q | equal | equal | greater = false
tieBefore? p q | equal | equal | equal
    with cmpMaybeBinderPresence (profileRight p) (profileRight q)
tieBefore? p q | equal | equal | equal | less = true
tieBefore? p q | equal | equal | equal | greater = false
tieBefore? p q | equal | equal | equal | equal
    with cmpMaybeBinderExposure (profileRight p) (profileRight q)
tieBefore? p q | equal | equal | equal | equal | less = true
tieBefore? p q | equal | equal | equal | equal | greater = false
tieBefore? p q | equal | equal | equal | equal | equal =
  profileCreation p <ᵇ profileCreation q

hasLeft? : Profile → Bool
hasLeft? p with profileLeft p
hasLeft? p | just b = true
hasLeft? p | nothing = false

hasRight? : Profile → Bool
hasRight? p with profileRight p
hasRight? p | just b = true
hasRight? p | nothing = false

leftBefore? : Profile → Profile → Bool
leftBefore? p q = cmpToBool (cmpMaybeBinderExposure (profileLeft p)
                                                    (profileLeft q))

rightBefore? : Profile → Profile → Bool
rightBefore? p q = cmpToBool (cmpMaybeBinderExposure (profileRight p)
                                                     (profileRight q))

Edge : Set
Edge = ℕ × ℕ

chainEdges : List Profile → List Edge
chainEdges [] = []
chainEdges (p ∷ []) = []
chainEdges (p ∷ q ∷ ps) =
  (profileId p , profileId q) ∷ chainEdges (q ∷ ps)

incomingFromRemaining? : ℕ → List Profile → List Edge → Bool
incomingFromRemaining? id remaining [] = false
incomingFromRemaining? id remaining ((src , dst) ∷ es)
    with dst ==ᵇ id | memberProfileId? src remaining
incomingFromRemaining? id remaining ((src , dst) ∷ es) | true | true = true
incomingFromRemaining? id remaining ((src , dst) ∷ es) | _ | _ =
  incomingFromRemaining? id remaining es

source? : List Edge → List Profile → Profile → Bool
source? edges remaining p =
  notᵇ (incomingFromRemaining? (profileId p) remaining edges)

sources : List Edge → List Profile → List Profile
sources edges remaining = filterᵇ (source? edges remaining) remaining

chooseMin : List Profile → Maybe Profile
chooseMin [] = nothing
chooseMin (p ∷ ps) = just (go p ps)
  where
    go : Profile → List Profile → Profile
    go best [] = best
    go best (p ∷ ps) with tieBefore? p best
    go best (p ∷ ps) | true = go p ps
    go best (p ∷ ps) | false = go best ps

topo :
  ℕ → List Edge → List Profile → List Profile → Maybe (List Profile)
topo fuel edges ordered [] = just ordered
topo zero edges ordered remaining = nothing
topo (suc fuel) edges ordered remaining with sources edges remaining
topo (suc fuel) edges ordered remaining | [] = nothing
topo (suc fuel) edges ordered remaining | srcs with chooseMin srcs
topo (suc fuel) edges ordered remaining | srcs | nothing = nothing
topo (suc fuel) edges ordered remaining | srcs | just p =
  topo fuel edges (ordered ++ (p ∷ [])) (removeProfile p remaining)

orderProfiles : Block → Maybe (List Profile)
orderProfiles b =
  topo (suc (length profiles)) edges [] profiles
  where
    profiles = blockProfiles b
    lefts = sortBy leftBefore? (filterᵇ hasLeft? profiles)
    rights = sortBy rightBefore? (filterᵇ hasRight? profiles)
    edges = chainEdges lefts ++ chainEdges rights

------------------------------------------------------------------------
-- Resolving profile placeholders
------------------------------------------------------------------------

findProfileInList : ℕ → List Profile → Maybe Profile
findProfileInList id [] = nothing
findProfileInList id (p ∷ ps) with id ==ᵇ profileId p
findProfileInList id (p ∷ ps) | true = just p
findProfileInList id (p ∷ ps) | false = findProfileInList id ps

profileByIdBlocks : ℕ → List Block → Maybe Profile
profileByIdBlocks id [] = nothing
profileByIdBlocks id (b ∷ bs) with findProfileInList id (blockProfiles b)
profileByIdBlocks id (b ∷ bs) | just p = just p
profileByIdBlocks id (b ∷ bs) | nothing = profileByIdBlocks id bs

profileById : ℕ → Solver → Maybe Profile
profileById id s = profileByIdBlocks id (blocks s)

Position : Set
Position = ℕ × ℕ

positionsFrom : ℕ → List Profile → List Position
positionsFrom n [] = []
positionsFrom n (p ∷ ps) = (profileId p , n) ∷ positionsFrom (suc n) ps

lookupPosition : ℕ → List Position → Maybe ℕ
lookupPosition id [] = nothing
lookupPosition id ((pid , pos) ∷ ps) with id ==ᵇ pid
lookupPosition id ((pid , pos) ∷ ps) | true = just pos
lookupPosition id ((pid , pos) ∷ ps) | false = lookupPosition id ps

resolveBlockRefs :
  ℕ → List Position → ℕ → RawTy → ℕ → Solver → Maybe RawTy
resolveBlockRefs bid pos count (rawVar (rawProfile pid)) depth s
    with profileById pid s
resolveBlockRefs bid pos count (rawVar (rawProfile pid)) depth s
    | nothing = nothing
resolveBlockRefs bid pos count (rawVar (rawProfile pid)) depth s
    | just p with profileBlock p ==ᵇ bid
resolveBlockRefs bid pos count (rawVar (rawProfile pid)) depth s
    | just p | false = just (rawVar (rawProfile pid))
resolveBlockRefs bid pos count (rawVar (rawProfile pid)) depth s
    | just p | true with lookupPosition pid pos
resolveBlockRefs bid pos count (rawVar (rawProfile pid)) depth s
    | just p | true | nothing = nothing
resolveBlockRefs bid pos count (rawVar (rawProfile pid)) depth s
    | just p | true | just index =
      just (rawVar (rawBound (depth + (count ∸ suc index))))
resolveBlockRefs bid pos count (rawVar ref) depth s = just (rawVar ref)
resolveBlockRefs bid pos count (rawBase ι) depth s = just (rawBase ι)
resolveBlockRefs bid pos count rawStar depth s = just rawStar
resolveBlockRefs bid pos count (rawArr A B) depth s
    with resolveBlockRefs bid pos count A depth s
resolveBlockRefs bid pos count (rawArr A B) depth s | nothing = nothing
resolveBlockRefs bid pos count (rawArr A B) depth s | just A′
    with resolveBlockRefs bid pos count B depth s
resolveBlockRefs bid pos count (rawArr A B) depth s | just A′ | nothing =
  nothing
resolveBlockRefs bid pos count (rawArr A B) depth s | just A′ | just B′ =
  just (rawArr A′ B′)
resolveBlockRefs bid pos count (rawAll A) depth s
    with resolveBlockRefs bid pos count A (suc depth) s
resolveBlockRefs bid pos count (rawAll A) depth s | nothing = nothing
resolveBlockRefs bid pos count (rawAll A) depth s | just A′ =
  just (rawAll A′)

wrapAll : List Profile → RawTy → RawTy
wrapAll [] A = A
wrapAll (p ∷ ps) A = rawAll (wrapAll ps A)

closeBlock : ℕ → RawTy → Solver → Maybe (RawTy × Solver)
closeBlock bid body s with lookupBlock bid (blocks s)
closeBlock bid body s | nothing = nothing
closeBlock bid body s | just b
    with pairUnused (unusedLeft b) (unusedRight b) b s
closeBlock bid body s | just b | nothing = nothing
closeBlock bid body s | just b | just (b′ , s′) with orderProfiles b′
closeBlock bid body s | just b | just (b′ , s′) | nothing = nothing
closeBlock bid body s | just b | just (b′ , s′) | just ordered
    with resolveBlockRefs bid (positionsFrom 0 ordered) (length ordered)
                          body 0 s′
closeBlock bid body s | just b | just (b′ , s′) | just ordered | nothing =
  nothing
closeBlock bid body s | just b | just (b′ , s′) | just ordered | just body′ =
  just (wrapAll ordered body′ , s′)

------------------------------------------------------------------------
-- Recursive endpoint-canonical computation
------------------------------------------------------------------------

exposeForalls :
  Side → Ty → Env → ℕ → Solver → Ty × (Env × Solver)
exposeForalls side (`∀ A) env bid s with lookupBlock bid (blocks s)
exposeForalls side (`∀ A) env bid s | nothing = `∀ A , (env , s)
exposeForalls side (`∀ A) env bid s | just b
    with freshBinder side b s
exposeForalls side (`∀ A) env bid s | just b | binder , (b′ , s′) =
  exposeForalls side A (binder ∷ env) bid s′
exposeForalls side A env bid s = A , (env , s)

mutual
  mlbBlock :
    ℕ → Ty → Ty → Env → Env → Solver → Maybe (RawTy × Solver)
  mlbBlock zero A B leftEnv rightEnv s = nothing
  mlbBlock (suc fuel) A B leftEnv rightEnv s
      with freshBlock s
  mlbBlock (suc fuel) A B leftEnv rightEnv s | block , s₁
      with exposeForalls leftSide A leftEnv (blockId block) s₁
  mlbBlock (suc fuel) A B leftEnv rightEnv s | block , s₁
      | A′ , (leftEnv′ , s₂)
      with exposeForalls rightSide B rightEnv (blockId block) s₂
  mlbBlock (suc fuel) A B leftEnv rightEnv s | block , s₁
      | A′ , (leftEnv′ , s₂) | B′ , (rightEnv′ , s₃)
      with mlbBody fuel A′ B′ leftEnv′ rightEnv′ s₃
  mlbBlock (suc fuel) A B leftEnv rightEnv s | block , s₁
      | A′ , (leftEnv′ , s₂) | B′ , (rightEnv′ , s₃) | nothing =
      nothing
  mlbBlock (suc fuel) A B leftEnv rightEnv s | block , s₁
      | A′ , (leftEnv′ , s₂) | B′ , (rightEnv′ , s₃)
      | just (body , s₄) =
      closeBlock (blockId block) body s₄

  mlbBody :
    ℕ → Ty → Ty → Env → Env → Solver → Maybe (RawTy × Solver)
  mlbBody zero A B leftEnv rightEnv s = nothing
  mlbBody (suc fuel) (`∀ A) B leftEnv rightEnv s =
    mlbBlock fuel (`∀ A) B leftEnv rightEnv s
  mlbBody (suc fuel) A (`∀ B) leftEnv rightEnv s =
    mlbBlock fuel A (`∀ B) leftEnv rightEnv s
  mlbBody (suc fuel) ★ ★ leftEnv rightEnv s = just (rawStar , s)
  mlbBody (suc fuel) (‵ ι) (‵ ι′) leftEnv rightEnv s
      with ι ≟Base ι′
  mlbBody (suc fuel) (‵ ι) (‵ .ι) leftEnv rightEnv s | yes refl =
    just (rawBase ι , s)
  mlbBody (suc fuel) (‵ ι) (‵ ι′) leftEnv rightEnv s | no neq =
    nothing
  mlbBody (suc fuel) (‵ ι) ★ leftEnv rightEnv s = just (rawBase ι , s)
  mlbBody (suc fuel) ★ (‵ ι) leftEnv rightEnv s = just (rawBase ι , s)
  mlbBody (suc fuel) (A₁ ⇒ A₂) (B₁ ⇒ B₂) leftEnv rightEnv s
      with mlbBody fuel A₁ B₁ leftEnv rightEnv s
  mlbBody (suc fuel) (A₁ ⇒ A₂) (B₁ ⇒ B₂) leftEnv rightEnv s
      | nothing = nothing
  mlbBody (suc fuel) (A₁ ⇒ A₂) (B₁ ⇒ B₂) leftEnv rightEnv s
      | just (C₁ , s₁) with mlbBody fuel A₂ B₂ leftEnv rightEnv s₁
  mlbBody (suc fuel) (A₁ ⇒ A₂) (B₁ ⇒ B₂) leftEnv rightEnv s
      | just (C₁ , s₁) | nothing = nothing
  mlbBody (suc fuel) (A₁ ⇒ A₂) (B₁ ⇒ B₂) leftEnv rightEnv s
      | just (C₁ , s₁) | just (C₂ , s₂) =
      just (rawArr C₁ C₂ , s₂)
  mlbBody (suc fuel) (A₁ ⇒ A₂) ★ leftEnv rightEnv s
      with mlbBody fuel A₁ ★ leftEnv rightEnv s
  mlbBody (suc fuel) (A₁ ⇒ A₂) ★ leftEnv rightEnv s
      | nothing = nothing
  mlbBody (suc fuel) (A₁ ⇒ A₂) ★ leftEnv rightEnv s
      | just (C₁ , s₁) with mlbBody fuel A₂ ★ leftEnv rightEnv s₁
  mlbBody (suc fuel) (A₁ ⇒ A₂) ★ leftEnv rightEnv s
      | just (C₁ , s₁) | nothing = nothing
  mlbBody (suc fuel) (A₁ ⇒ A₂) ★ leftEnv rightEnv s
      | just (C₁ , s₁) | just (C₂ , s₂) =
      just (rawArr C₁ C₂ , s₂)
  mlbBody (suc fuel) ★ (B₁ ⇒ B₂) leftEnv rightEnv s
      with mlbBody fuel ★ B₁ leftEnv rightEnv s
  mlbBody (suc fuel) ★ (B₁ ⇒ B₂) leftEnv rightEnv s
      | nothing = nothing
  mlbBody (suc fuel) ★ (B₁ ⇒ B₂) leftEnv rightEnv s
      | just (C₁ , s₁) with mlbBody fuel ★ B₂ leftEnv rightEnv s₁
  mlbBody (suc fuel) ★ (B₁ ⇒ B₂) leftEnv rightEnv s
      | just (C₁ , s₁) | nothing = nothing
  mlbBody (suc fuel) ★ (B₁ ⇒ B₂) leftEnv rightEnv s
      | just (C₁ , s₁) | just (C₂ , s₂) =
      just (rawArr C₁ C₂ , s₂)
  mlbBody (suc fuel) (＇ X) (＇ Y) leftEnv rightEnv s
      with lookupEnv leftEnv X | lookupEnv rightEnv Y
  mlbBody (suc fuel) (＇ X) (＇ Y) leftEnv rightEnv s
      | boundRef l | boundRef r with requestProfile (just l) (just r) s
  mlbBody (suc fuel) (＇ X) (＇ Y) leftEnv rightEnv s
      | boundRef l | boundRef r | nothing = nothing
  mlbBody (suc fuel) (＇ X) (＇ Y) leftEnv rightEnv s
      | boundRef l | boundRef r | just (p , s′) =
      just (rawVar (rawProfile (profileId p)) , s′)
  mlbBody (suc fuel) (＇ X) (＇ Y) leftEnv rightEnv s
      | boundRef l | freeRef j = nothing
  mlbBody (suc fuel) (＇ X) (＇ Y) leftEnv rightEnv s
      | freeRef i | boundRef r = nothing
  mlbBody (suc fuel) (＇ X) (＇ Y) leftEnv rightEnv s
      | freeRef i | freeRef j with i ==ᵇ j
  mlbBody (suc fuel) (＇ X) (＇ Y) leftEnv rightEnv s
      | freeRef i | freeRef j | true = just (rawVar (rawFree i) , s)
  mlbBody (suc fuel) (＇ X) (＇ Y) leftEnv rightEnv s
      | freeRef i | freeRef j | false = nothing
  mlbBody (suc fuel) (＇ X) ★ leftEnv rightEnv s
      with lookupEnv leftEnv X
  mlbBody (suc fuel) (＇ X) ★ leftEnv rightEnv s | freeRef i =
    nothing
  mlbBody (suc fuel) (＇ X) ★ leftEnv rightEnv s | boundRef l
      with requestProfile (just l) nothing s
  mlbBody (suc fuel) (＇ X) ★ leftEnv rightEnv s | boundRef l
      | nothing = nothing
  mlbBody (suc fuel) (＇ X) ★ leftEnv rightEnv s | boundRef l
      | just (p , s′) = just (rawVar (rawProfile (profileId p)) , s′)
  mlbBody (suc fuel) ★ (＇ Y) leftEnv rightEnv s
      with lookupEnv rightEnv Y
  mlbBody (suc fuel) ★ (＇ Y) leftEnv rightEnv s | freeRef i =
    nothing
  mlbBody (suc fuel) ★ (＇ Y) leftEnv rightEnv s | boundRef r
      with requestProfile nothing (just r) s
  mlbBody (suc fuel) ★ (＇ Y) leftEnv rightEnv s | boundRef r
      | nothing = nothing
  mlbBody (suc fuel) ★ (＇ Y) leftEnv rightEnv s | boundRef r
      | just (p , s′) = just (rawVar (rawProfile (profileId p)) , s′)
  mlbBody (suc fuel) (＇ X) (‵ ι) leftEnv rightEnv s = nothing
  mlbBody (suc fuel) (＇ X) (B₁ ⇒ B₂) leftEnv rightEnv s = nothing
  mlbBody (suc fuel) (‵ ι) (＇ Y) leftEnv rightEnv s = nothing
  mlbBody (suc fuel) (‵ ι) (B₁ ⇒ B₂) leftEnv rightEnv s = nothing
  mlbBody (suc fuel) (A₁ ⇒ A₂) (＇ Y) leftEnv rightEnv s = nothing
  mlbBody (suc fuel) (A₁ ⇒ A₂) (‵ ι) leftEnv rightEnv s = nothing

------------------------------------------------------------------------
-- Public Maybe-valued endpoint-canonical surface
------------------------------------------------------------------------

sizeTy : Ty → ℕ
sizeTy (＇ X) = 1
sizeTy (‵ ι) = 1
sizeTy ★ = 1
sizeTy (A ⇒ B) = suc (sizeTy A + sizeTy B)
sizeTy (`∀ A) = suc (sizeTy A)

fuelFor : Ty → Ty → ℕ
fuelFor A B = 20 + sizeTy A + sizeTy B + sizeTy A + sizeTy B

rawToTy : ℕ → RawTy → Maybe Ty
rawToTy depth (rawVar (rawBound X)) = just (＇ X)
rawToTy depth (rawVar (rawFree X)) = just (＇ (depth + X))
rawToTy depth (rawVar (rawProfile id)) = nothing
rawToTy depth (rawBase ι) = just (‵ ι)
rawToTy depth rawStar = just ★
rawToTy depth (rawArr A B) with rawToTy depth A
rawToTy depth (rawArr A B) | nothing = nothing
rawToTy depth (rawArr A B) | just A′ with rawToTy depth B
rawToTy depth (rawArr A B) | just A′ | nothing = nothing
rawToTy depth (rawArr A B) | just A′ | just B′ = just (A′ ⇒ B′)
rawToTy depth (rawAll A) with rawToTy (suc depth) A
rawToTy depth (rawAll A) | nothing = nothing
rawToTy depth (rawAll A) | just A′ = just (`∀ A′)

endpointMlb : Ty → Ty → Maybe Ty
endpointMlb A B with mlbBlock (fuelFor A B) A B [] [] initialSolver
endpointMlb A B | nothing = nothing
endpointMlb A B | just (raw , s) = rawToTy 0 raw
