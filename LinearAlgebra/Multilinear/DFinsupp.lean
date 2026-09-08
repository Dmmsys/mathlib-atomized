/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Sophie Morel
-/
module

public import Mathlib.Data.Fintype.Quotient
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Interactions between finitely-supported functions and multilinear maps

## Main definitions

* `MultilinearMap.dfinsupp_ext`
* `MultilinearMap.dfinsuppFamily`, which satisfies
  `dfinsuppFamily f x p = f p (fun i => x i (p i))`.

  This is the finitely-supported version of `MultilinearMap.piFamily`.

  This is useful because all the intermediate results are bundled:

  - `MultilinearMap.dfinsuppFamily f x` is a `DFinsupp` supported by families of indices `p`.
  - `MultilinearMap.dfinsuppFamily f` is a `MultilinearMap` operating on finitely-supported
    functions `x`.
  - `MultilinearMap.dfinsuppFamilyₗ` is a `LinearMap`, linear in the family of multilinear maps `f`.

* `freeDFinsuppEquiv` is an equivalence of multilinear maps over free modules with finitely
  supported maps.

-/

@[expose] public section

universe uι uκ uS uR uM uN
variable {ι : Type uι} {κ : ι → Type uκ}
variable {S : Type uS} {R : Type uR}

namespace MultilinearMap

section Semiring
variable {M : ∀ i, κ i → Type uM} {N : Type uN}

variable [Finite ι] [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [AddCommMonoid N]
variable [∀ i k, Module R (M i k)] [Module R N]

/-- Two multilinear maps from finitely supported functions are equal if they agree on the
generators.

This is a multilinear version of `DFinsupp.lhom_ext'`. -/
@[ext]
/-
**MultilinearMap.dfinsupp_ext** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：dfinsupp_ext [forall i, DecidableEq (κ i)] ⦃f g : MultilinearMap R (fun i 
=> Π₀ j : κ i, M i j) N⦄ (h : forall p : Π i, κ i, f.compLinearMap (fun i => DFi
nsupp.lsingle (p i)) = g.compLinearMap (fun i => DFinsupp.lsingle (p i))) : f = 
g
参数：κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.sum_single`：sum_single [forall i, AddCommMonoid (β i)] [forall 
(i) (x : β i), Decidable (x != 0)] {f : Π₀ i, β i} : f.sum single = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MultilinearMap.map_sum_finset`：map_sum_finset [DecidableEq ι] [Fintype ι
] : (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Two multilinear maps from finitely supported functions are equal if they agree o
n the
generators.

This is a multilinear version of `DFinsupp.lhom_ext'`.
-/
theorem dfinsupp_ext [∀ i, DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i ↦ Π₀ j : κ i, M i j) N⦄
    (h : ∀ p : Π i, κ i,
      f.compLinearMap (fun i => DFinsupp.lsingle (p i)) =
      g.compLinearMap (fun i => DFinsupp.lsingle (p i))) : f = g := by
  ext x
  change f (fun i ↦ x i) = g (fun i ↦ x i)
  classical
  cases nonempty_fintype ι
  rw [funext (fun i ↦ Eq.symm (DFinsupp.sum_single (f := x i)))]
  simp_rw [DFinsupp.sum, MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

end Semiring

section dfinsuppFamily
variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

section Semiring

variable [DecidableEq ι] [Fintype ι] [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

set_option backward.isDefEq.respectTransparency false in
/--
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to select one index from
each family, `dfinsuppFamily f` maps a family of finitely-supported functions (one for each domain
`κ i`) into a finitely-supported function from each selection of indices (with domain `Π i, κ i`).

Strictly this doesn't need multilinearity, only the fact that `f p m = 0` whenever `m i = 0` for
some `i`.

This is the `DFinsupp` version of `MultilinearMap.piFamily`.
-/
@[simps]
/-
**MultilinearMap.dfinsuppFamily** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：dfinsuppFamily (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)
) (N p)) : MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) 
where toFun x
参数：f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to se
lect one index from
each family, `dfinsuppFamily f` maps a family of finitely-supported functions (o
ne for each domain
`κ i`) into a finitely-supported function from each selection of indices (with d
omain `Π i, κ i`).

Strictly this doesn't need multilinearity, only the fact that `f p m = 0` whenev
er `m i = 0` for
some `i`.

This is the `DFinsupp` version of `MultilinearMap.piFamily`.
-/
def dfinsuppFamily
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) where
  toFun x :=
  { toFun := fun p => f p (fun i => x i (p i))
    support' := (Trunc.finChoice fun i => (x i).support').map fun s => ⟨
      Finset.univ.val.pi (fun i ↦ (s i).val) |>.map fun f i => f i (Finset.mem_univ _),
      fun p => by
        simp only [Multiset.mem_map, Multiset.mem_pi, Finset.mem_val, Finset.mem_univ,
          forall_true_left]
        simp_rw [or_iff_not_imp_right]
        intro h
        push Not at h
        refine ⟨fun i _ => p i, fun i => (s i).prop _ |>.resolve_right ?_, rfl⟩
        exact mt ((f p).map_coord_zero (m := fun i => x i _) i) h⟩}
  map_update_add' {dec} m i x y := DFinsupp.ext fun p => by
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, DFinsupp.add_apply, (f p).map_update_add]
  map_update_smul' {dec} m i c x := DFinsupp.ext fun p => by
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, DFinsupp.smul_apply,
      (f p).map_update_smul]
/-
**MultilinearMap.support_dfinsuppFamily_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multil
inearMap`。
形式化陈述：support_dfinsuppFamily_subset [forall i, DecidableEq (κ i)] [forall i j, (
x : M i j) -> Decidable (x != 0)] [forall i, (x : N i) -> Decidable (x != 0)] (f
 : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)) (x : forall i,
 Π₀ j : κ i, M i j) : (dfinsuppFamily f x).support subseteq Fintype.piFinset fun
 i => (x i).support
参数：κ i；x : M i j；x != 0；x : N i；x != 0；f : Π (p : Π i, κ i), MultilinearMap R (f
un i => M i (p i)) (N p)；x : forall i, Π₀ j : κ i, M i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.dfinsuppFamily_apply_toFun`：∀ {ι : Type uι} {κ : ι → Type
 uκ} {R : Type uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}
   [inst : DecidableEq ι] [inst…
-/
theorem support_dfinsuppFamily_subset
    [∀ i, DecidableEq (κ i)]
    [∀ i j, (x : M i j) → Decidable (x ≠ 0)] [∀ i, (x : N i) → Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (x : ∀ i, Π₀ j : κ i, M i j) :
    (dfinsuppFamily f x).support ⊆ Fintype.piFinset fun i => (x i).support := by
  intro p hp
  simp only [DFinsupp.mem_support_toFun, dfinsuppFamily_apply_toFun, ne_eq,
    Fintype.mem_piFinset] at hp ⊢
  intro i
  exact mt ((f p).map_coord_zero (m := fun i => x i _) i) hp

/-- When applied to a family of finitely-supported functions each supported on a single element,
`dfinsuppFamily` is itself supported on a single element, with value equal to the map `f` applied
at that point. -/
@[simp]
/-
**MultilinearMap.dfinsuppFamily_single** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap
`。
形式化陈述：dfinsuppFamily_single [forall i, DecidableEq (κ i)] (f : Π (p : Π i, κ i),
 MultilinearMap R (fun i => M i (p i)) (N p)) (p : forall i, κ i) (m : forall i,
 M i (p i)) : dfinsuppFamily f (fun i => .single (p i) (m i)) = DFinsupp.single 
p (f p m)
参数：κ i；f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)；p : for
all i, κ i；m : forall i, M i (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.dfinsuppFamily_apply_toFun`：∀ {ι : Type uι} {κ : ι → Type
 uκ} {R : Type uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}
   [inst : DecidableEq ι] [inst…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
When applied to a family of finitely-supported functions each supported on a sin
gle element,
`dfinsuppFamily` is itself supported on a single element, with value equal to th
e map `f` applied
at that point.
-/
theorem dfinsuppFamily_single [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    dfinsuppFamily f (fun i => .single (p i) (m i)) = DFinsupp.single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne q p
  · simp
  · rw [DFinsupp.single_eq_of_ne hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [DFinsupp.single_eq_of_ne hpqi]

/-- When only one member of the family of multilinear maps is nonzero, the result consists only of
the component from that member. -/
@[simp]
/-
**MultilinearMap.dfinsuppFamily_single_left_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mul
tilinearMap`。
形式化陈述：dfinsuppFamily_single_left_apply [forall i, DecidableEq (κ i)] (p : Π i, κ
 i) (f : MultilinearMap R (fun i => M i (p i)) (N p)) (x : Π i, Π₀ j, M i j) : d
finsuppFamily (Pi.single p f) x = DFinsupp.single p (f fun i => x _ (p i))
参数：κ i；p : Π i, κ i；f : MultilinearMap R (fun i => M i (p i)) (N p)；x : Π i, Π₀ 
j, M i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.dfinsuppFamily_apply_toFun`：∀ {ι : Type uι} {κ : ι → Type
 uκ} {R : Type uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}
   [inst : DecidableEq ι] [inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MultilinearMap.instIsZeroApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ 
: ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] [inst_2 : Ad…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯

--- 原说明 ---
When only one member of the family of multilinear maps is nonzero, the result co
nsists only of
the component from that member.
-/
theorem dfinsuppFamily_single_left_apply [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) (x : Π i, Π₀ j, M i j) :
    dfinsuppFamily (Pi.single p f) x = DFinsupp.single p (f fun i => x _ (p i)) := by
  ext p'
  obtain rfl | hp := eq_or_ne p p'
  · simp
  · simp [hp]
/-
**MultilinearMap.dfinsuppFamily_single_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiline
arMap`。
形式化陈述：dfinsuppFamily_single_left [forall i, DecidableEq (κ i)] (p : Π i, κ i) (f
 : MultilinearMap R (fun i => M i (p i)) (N p)) : dfinsuppFamily (Pi.single p f)
 = (DFinsupp.lsingle p).compMultilinearMap (f.compLinearMap fun i => DFinsupp.la
pply (p i))
参数：κ i；p : Π i, κ i；f : MultilinearMap R (fun i => M i (p i)) (N p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `MultilinearMap.dfinsuppFamily_single_left_apply`：dfinsuppFamily_single_l
eft_apply [forall i, DecidableEq (κ i)] (p : Π i, κ i) (f : MultilinearMap R (fu
n i => M i (p i)) (N p)) (x : Π i, Π₀…
-/
theorem dfinsuppFamily_single_left [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    dfinsuppFamily (Pi.single p f) =
      (DFinsupp.lsingle p).compMultilinearMap (f.compLinearMap fun i => DFinsupp.lapply (p i)) :=
  ext <| dfinsuppFamily_single_left_apply _ _

@[simp]
/-
**MultilinearMap.dfinsuppFamily_compLinearMap_lsingle** 是 Mathlib 中的一个定理，位于命名空间 
`MultilinearMap`。
形式化陈述：dfinsuppFamily_compLinearMap_lsingle [forall i, DecidableEq (κ i)] (f : Π 
(p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)) (p : forall i, κ i)
 : (dfinsuppFamily f).compLinearMap (fun i => DFinsupp.lsingle (p i)) = (DFinsup
p.lsingle p).compMultilinearMap (f p)
参数：κ i；f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)；p : for
all i, κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `MultilinearMap.dfinsuppFamily_single`：dfinsuppFamily_single [forall i, D
ecidableEq (κ i)] (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (
N p)) (p : forall i, κ i) …
-/
theorem dfinsuppFamily_compLinearMap_lsingle [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) (p : ∀ i, κ i) :
    (dfinsuppFamily f).compLinearMap (fun i => DFinsupp.lsingle (p i))
      = (DFinsupp.lsingle p).compMultilinearMap (f p) :=
  MultilinearMap.ext <| dfinsuppFamily_single f p

@[simp]
/-
**MultilinearMap.dfinsuppFamily_zero** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：dfinsuppFamily_zero : dfinsuppFamily (0 : Π (p : Π i, κ i), MultilinearMap
 R (fun i => M i (p i)) (N p)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.dfinsuppFamily_apply_toFun`：∀ {ι : Type uι} {κ : ι → Type
 uκ} {R : Type uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}
   [inst : DecidableEq ι] [inst…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MultilinearMap.instIsZeroApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ 
: ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] [inst_2 : Ad…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dfinsuppFamily_zero :
    dfinsuppFamily (0 : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) = 0 := by
  ext; simp

@[simp]
/-
**MultilinearMap.dfinsuppFamily_add** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：dfinsuppFamily_add (f g : Π (p : Π i, κ i), MultilinearMap R (fun i => M i
 (p i)) (N p)) : dfinsuppFamily (f + g) = dfinsuppFamily f + dfinsuppFamily g
参数：f g : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.dfinsuppFamily_apply_toFun`：∀ {ι : Type uι} {κ : ι → Type
 uκ} {R : Type uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}
   [inst : DecidableEq ι] [inst…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MultilinearMap.instIsAddApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ :
 ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMo
noid (M₁ i)] [inst_2 : Ad…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dfinsuppFamily_add (f g : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    dfinsuppFamily (f + g) = dfinsuppFamily f + dfinsuppFamily g := by
  ext; simp

@[simp]
/-
**MultilinearMap.dfinsuppFamily_smul** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：dfinsuppFamily_smul [Monoid S] [forall p, DistribMulAction S (N p)] [foral
l p, SMulCommClass R S (N p)] (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (f
un i => M i (p i)) (N p)) : dfinsuppFamily (s • f) = s • dfinsuppFamily f
参数：N p；N p；s : S；f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N 
p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.dfinsuppFamily_apply_toFun`：∀ {ι : Type uι} {κ : ι → Type
 uκ} {R : Type uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}
   [inst : DecidableEq ι] [inst…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MultilinearMap.instIsSMulApplyForall`：∀ {R : Type uR} {S : Type uS} {ι :
 Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i :
 ι) → AddCommMonoid (M₁ i)…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dfinsuppFamily_smul
    [Monoid S] [∀ p, DistribMulAction S (N p)] [∀ p, SMulCommClass R S (N p)]
    (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    dfinsuppFamily (s • f) = s • dfinsuppFamily f := by
  ext; simp

end Semiring

section CommSemiring

variable [DecidableEq ι] [Fintype ι] [CommSemiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

/-- `MultilinearMap.dfinsuppFamily` as a linear map. -/
@[simps]
/-
**MultilinearMap.dfinsuppFamily** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：dfinsuppFamily (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)
) (N p)) : MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) 
where toFun x
参数：f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
`MultilinearMap.dfinsuppFamily` as a linear map.
-/
def dfinsuppFamilyₗ :
    (Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
      →ₗ[R] MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) where
  toFun := dfinsuppFamily
  map_add' := dfinsuppFamily_add
  map_smul' := dfinsuppFamily_smul

variable {N : Type*} [AddCommMonoid N] [Module R N] [(i : ι) → DecidableEq (κ i)]

variable (R κ) in
/-- The linear equivalence between families indexed by `p : Π i : ι, κ i` of multilinear maps
on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ Π₀ j : κ i, M i j`. -/
/-
**MultilinearMap.fromDFinsuppEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：fromDFinsuppEquiv : ((p : Π i, κ i) -> MultilinearMap R (fun i => M i (p i
)) N) ≃ₗ[R] MultilinearMap R (fun i => Π₀ j : κ i, M i j) N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between families indexed by `p : Π i : ι, κ i` of multili
near maps
on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ Π₀ j : κ
 i, M i j`.
-/
def fromDFinsuppEquiv :
    ((p : Π i, κ i) → MultilinearMap R (fun i ↦ M i (p i)) N) ≃ₗ[R]
      MultilinearMap R (fun i ↦ Π₀ j : κ i, M i j) N :=
  LinearEquiv.ofLinearMap
    ((DFinsupp.lsum ℕ fun _ ↦ .id).compMultilinearMapₗ R ∘ₗ MultilinearMap.dfinsuppFamilyₗ)
    (LinearMap.pi fun p ↦ MultilinearMap.compLinearMapₗ fun i ↦ DFinsupp.lsingle (p i))
    (by ext f x; simp)
    (by ext f p a; simp)

@[simp]
/-
**MultilinearMap.fromDFinsuppEquiv_single** 是 Mathlib 中的一个定理，位于命名空间 `Multilinear
Map`。
形式化陈述：fromDFinsuppEquiv_single (f : Π (p : Π i, κ i), MultilinearMap R (fun i =>
 M i (p i)) N) (p : Π i, κ i) (x : Π i, M i (p i)) : fromDFinsuppEquiv κ R f (fu
n i => DFinsupp.single (p i) (x i)) = f p x
参数：f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) N；p : Π i, κ i；x 
: Π i, M i (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.dfinsuppFamilyₗ_apply`：∀ {ι : Type uι} {κ : ι → Type uκ} 
{R : Type uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}   [i
nst : DecidableEq ι] [inst…
· 使用定理 `LinearMap.compMultilinearMapₗ_apply`：∀ {R : Type uR} (S : Type uS) {ι : 
Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} [inst : Semiring R]   
[inst_1 : (i : ι) → AddCo…
· 使用定理 `MultilinearMap.dfinsuppFamily_single`：dfinsuppFamily_single [forall i, D
ecidableEq (κ i)] (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (
N p)) (p : forall i, κ i) …
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fromDFinsuppEquiv_single
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) N)
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    fromDFinsuppEquiv κ R f (fun i => DFinsupp.single (p i) (x i)) = f p x := by
  simp [fromDFinsuppEquiv]
/-
**MultilinearMap.fromDFinsuppEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearM
ap`。
形式化陈述：fromDFinsuppEquiv_apply [Π i (j : κ i) (x : M i j), Decidable (x != 0)] (f
 : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) N) (x : Π i, Π₀ (j : 
κ i), M i j) : fromDFinsuppEquiv κ R f x = ∑ p in Fintype.piFinset (fun i => (x 
i).support), f p (fun i => x i (p i))
参数：j : κ i；x : M i j；x != 0；f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i
 (p i)) N；x : Π i, Π₀ (j : κ i), M i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `MultilinearMap.support_dfinsuppFamily_subset`：support_dfinsuppFamily_sub
set [forall i, DecidableEq (κ i)] [forall i j, (x : M i j) -> Decidable (x != 0)
] [forall i, (x : N i) -> Decidabl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.support.congr_simp`：∀ {ι : Type u} {β : ι → Type v} [inst : Dec
idableEq ι] [inst_1 : (i : ι) → Zero (β i)]   {inst_2 : (i : ι) → (x : β i) → De
cidable (x ≠ 0)} …
· 使用定理 `MultilinearMap.dfinsuppFamilyₗ_apply`：∀ {ι : Type uι} {κ : ι → Type uκ} 
{R : Type uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}   [i
nst : DecidableEq ι] [inst…
· 使用定理 `MultilinearMap.dfinsuppFamily_apply_toFun`：∀ {ι : Type uι} {κ : ι → Type
 uκ} {R : Type uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}
   [inst : DecidableEq ι] [inst…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fromDFinsuppEquiv_apply
    [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) N)
    (x : Π i, Π₀ (j : κ i), M i j) :
    fromDFinsuppEquiv κ R f x =
      ∑ p ∈ Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := by
  classical
  refine (DFinsupp.sumAddHom_apply _ _).trans ?_
  refine Finset.sum_subset (MultilinearMap.support_dfinsuppFamily_subset _ _) ?_
  simp

@[simp]
/-
**MultilinearMap.fromDFinsuppEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Multili
nearMap`。
形式化陈述：fromDFinsuppEquiv_symm_apply (f : MultilinearMap R (fun i => Π₀ j : κ i, M
 i j) N) (p : Π i, κ i) : (fromDFinsuppEquiv κ R).symm f p = f.compLinearMap (fu
n i => DFinsupp.lsingle (p i))
参数：f : MultilinearMap R (fun i => Π₀ j : κ i, M i j) N；p : Π i, κ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromDFinsuppEquiv_symm_apply (f : MultilinearMap R (fun i ↦ Π₀ j : κ i, M i j) N)
    (p : Π i, κ i) :
    (fromDFinsuppEquiv κ R).symm f p = f.compLinearMap (fun i ↦ DFinsupp.lsingle (p i)) :=
  rfl

end CommSemiring

end dfinsuppFamily

section freeDFinsuppEquiv

variable {ι' : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/--
The linear equivalence of multilinear maps on free modules over `R` indexed by `fun i => κ i` on
the domain and `ι'` on the codomain and the dependent, finitely supported maps from
`(Π i, κ i) × ι'` into `R`.
-/
/-
**MultilinearMap.freeDFinsuppEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：freeDFinsuppEquiv : (Π₀ (_ : (Π i, κ i) × ι'), R) ≃ₗ[R] MultilinearMap R (
fun i => Π₀ _ : κ i, R) (Π₀ _ : ι', R)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The linear equivalence of multilinear maps on free modules over `R` indexed by `
fun i => κ i` on
the domain and `ι'` on the codomain and the dependent, finitely supported maps f
rom
`(Π i, κ i) × ι'` into `R`.
-/
def freeDFinsuppEquiv :
    (Π₀ (_ : (Π i, κ i) × ι'), R) ≃ₗ[R] MultilinearMap R (fun i => Π₀ _ : κ i, R) (Π₀ _ : ι', R) :=
  (DFinsupp.domLCongr (M := fun _ => R) (Equiv.sigmaEquivProd _ _).symm) ≪≫ₗ
  (DFinsupp.sigmaCurryLEquiv (M := fun _ _ => R)) ≪≫ₗ
  DFinsupp.linearEquivFunOnFintype ≪≫ₗ
  LinearEquiv.piCongrRight (fun _ => MultilinearMap.piRingEquiv (ι := ι)) ≪≫ₗ
  fromDFinsuppEquiv κ R (M := fun _ _ => R)
/-
**MultilinearMap.freeDFinsuppEquiv_def** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap
`。
形式化陈述：freeDFinsuppEquiv_def (f : Π₀ (_ : (Π i, κ i) × ι'), R) : freeDFinsuppEqui
v f = fromDFinsuppEquiv κ R (LinearEquiv.piCongrRight (fun _ => MultilinearMap.p
iRingEquiv) <| DFinsupp.linearEquivFunOnFintype (R
参数：f : Π₀ (_ : (Π i, κ i) × ι'), R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem freeDFinsuppEquiv_def (f : Π₀ (_ : (Π i, κ i) × ι'), R) :
    freeDFinsuppEquiv f =
      fromDFinsuppEquiv κ R
      (LinearEquiv.piCongrRight (fun _ => MultilinearMap.piRingEquiv) <|
      DFinsupp.linearEquivFunOnFintype (R := R) <|
      DFinsupp.sigmaCurryLEquiv (R := R) <|
      (DFinsupp.domLCongr (R := R) (Equiv.sigmaEquivProd _ _).symm) f) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
When `freeDFinsuppEquiv` is applied to a map with a single value of one the resulting multilinear
map sends inputs to a single value in the codomain, taking a product over images from each
component of the domain.
-/
@[simp]
/-
**MultilinearMap.freeDFinsuppEquiv_single** 是 Mathlib 中的一个定理，位于命名空间 `Multilinear
Map`。
形式化陈述：freeDFinsuppEquiv_single [DecidableEq ι'] (p : (Π i, κ i) × ι') (r : R) (x
 : Π i, Π₀ _ : κ i, R) : freeDFinsuppEquiv (.single p r) x = r • .single p.2 ((∏
 i, (x i) (p.1 i)))
参数：p : (Π i, κ i) × ι'；r : R；x : Π i, Π₀ _ : κ i, R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `DFinsupp.single_smul`：single_smul {i : ι} (c : γ) (x : β i) : single i (
c • x) = c • single i x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MultilinearMap.instIsSMulApplyForall`：∀ {R : Type uR} {S : Type uS} {ι :
 Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i :
 ι) → AddCommMonoid (M₁ i)…
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MultilinearMap.mkPiRing_apply_one_eq_self`：mkPiRing_apply_one_eq_self [F
intype ι] (f : MultilinearMap R (fun _ : ι => R) M₂) : MultilinearMap.mkPiRing R
 ι (f fun _ => 1) = f
· 使用定理 `DFinsupp.domLCongr_apply`：∀ {ι : Type u_1} {ι' : Type u_2} {R : Type u_3
} {M : ι → Type u_5} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M 
i)] [inst_2 : …
· 使用定理 `DFinsupp.sigmaCurryLEquiv_apply`：∀ {ι : Type u_1} {R : Type u_3} [inst :
 Semiring R] [inst_1 : DecidableEq ι] {α : ι → Type u_7}   {M : (i : ι) → α i → 
Type u_8} [inst_2 : (…
· 使用定理 `MultilinearMap.fromDFinsuppEquiv_apply`：fromDFinsuppEquiv_apply [Π i (j 
: κ i) (x : M i j), Decidable (x != 0)] (f : Π (p : Π i, κ i), MultilinearMap R 
(fun i => M i (p i)) N) (x :…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DFinsupp.linearEquivFunOnFintype_apply`：∀ {ι : Type u_1} {R : Type u_3} 
{M : ι → Type u_5} [inst : Semiring R] [inst_1 : (i : ι) → AddCommMonoid (M i)] 
  [inst_2 : (i : ι) → _root_…
· 使用定理 `DFinsupp.finsetSum_apply`：finsetSum_apply {α} [forall i, AddCommMonoid (
β i)] (s : Finset α) (g : α -> Π₀ i, β i) (i : ι) : (∑ a in s, g a) i = ∑ a in s
, g a i
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
When `freeDFinsuppEquiv` is applied to a map with a single value of one the resu
lting multilinear
map sends inputs to a single value in the codomain, taking a product over images
 from each
component of the domain.
-/
theorem freeDFinsuppEquiv_single [DecidableEq ι'] (p : (Π i, κ i) × ι') (r : R)
    (x : Π i, Π₀ _ : κ i, R) :
    freeDFinsuppEquiv (.single p r) x = r • .single p.2 ((∏ i, (x i) (p.1 i))) := by
  classical
  conv_lhs => rw [← mul_one r, ← smul_eq_mul, DFinsupp.single_smul, map_smul, smul_apply]
  congr
  ext i
  obtain ⟨p, j⟩ := p
  rcases eq_or_ne j i with rfl | h
  · suffices ∀ (l : ι), (x l) (p l) = 0 → 0 = ∏ i, (x i) (p i) by
      simpa [freeDFinsuppEquiv_def, MultilinearMap.piRingEquiv, DFinsupp.sigmaCurryEquiv,
        fromDFinsuppEquiv_apply]
    exact fun i h ↦ (Finset.prod_eq_zero (Finset.mem_univ i) h).symm
  · simp [freeDFinsuppEquiv_def, MultilinearMap.piRingEquiv, DFinsupp.sigmaCurryEquiv,
      fromDFinsuppEquiv_apply, h]
/-
**MultilinearMap.freeDFinsuppEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearM
ap`。
形式化陈述：freeDFinsuppEquiv_apply [DecidableEq ι'] [Fintype ι'] (f : Π₀ (_ : (Π i, κ
 i) × ι'), R) (x : Π i, Π₀ _ : κ i, R) : freeDFinsuppEquiv f x = ∑ p, f p • .sin
gle p.2 ((∏ i, (x i) (p.1 i)))
参数：f : Π₀ (_ : (Π i, κ i) × ι'), R；x : Π i, Π₀ _ : κ i, R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.induction`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq 
ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   {p : (Π₀ (i : ι), β i) → Prop} (f :
 Π₀ (i :…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MultilinearMap.instIsZeroApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ 
: ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] [inst_2 : Ad…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MultilinearMap.instIsAddApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ :
 ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMo
noid (M₁ i)] [inst_2 : Ad…
· 使用定理 `MultilinearMap.freeDFinsuppEquiv_single`：freeDFinsuppEquiv_single [Decid
ableEq ι'] (p : (Π i, κ i) × ι') (r : R) (x : Π i, Π₀ _ : κ i, R) : freeDFinsupp
Equiv (.single p r) x = r • .…
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
（共 34 条，此处仅展示前 30 条）
-/
theorem freeDFinsuppEquiv_apply [DecidableEq ι'] [Fintype ι']
    (f : Π₀ (_ : (Π i, κ i) × ι'), R) (x : Π i, Π₀ _ : κ i, R) :
    freeDFinsuppEquiv f x = ∑ p, f p • .single p.2 ((∏ i, (x i) (p.1 i))) := by
  apply DFinsupp.induction f
  · simp
  · rintro p r f - - hfx
    simp [Finset.sum_add_distrib, add_smul, hfx]

end freeDFinsuppEquiv

end MultilinearMap

