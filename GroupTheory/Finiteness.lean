/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Finitely generated monoids and groups

We define finitely generated monoids and groups. See also `Submodule.FG` and `Module.Finite` for
finitely-generated modules.

## Main definition

* `Submonoid.FG S`, `AddSubmonoid.FG S` : A submonoid `S` is finitely generated.
* `Monoid.FG M`, `AddMonoid.FG M` : A typeclass indicating a type `M` is finitely generated as a
  monoid.
* `Subgroup.FG S`, `AddSubgroup.FG S` : A subgroup `S` is finitely generated.
* `Group.FG M`, `AddGroup.FG M` : A typeclass indicating a type `M` is finitely generated as a
  group.

-/

@[expose] public section

assert_not_exists MonoidWithZero

/-! ### Monoids and submonoids -/


open scoped Pointwise

variable {M N : Type*} [Monoid M]

section Submonoid
variable [Monoid N] {P : Submonoid M} {Q : Submonoid N}

/-- A submonoid of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
@[to_additive /-- An additive submonoid of `N` is finitely generated if it is the closure of a
finite subset of `M`. -/]
/-
**Submonoid.FG** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.FG (P : Submonoid M) : Prop
参数：P : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Submonoid.FG (P : Submonoid M) : Prop :=
  ∃ S : Finset M, Submonoid.closure ↑S = P

/-- An equivalent expression of `Submonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubmonoid.FG` in terms of `Set.Finite` instead of
`Finset`. -/]
/-
**Submonoid.fg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.fg_iff (P : Submonoid M) : Submonoid.FG P ↔ exists S : Set M, Su
bmonoid.closure S = P ∧ S.Finite
参数：P : Submonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submonoid.fg_iff (P : Submonoid M) :
    Submonoid.FG P ↔ ∃ S : Set M, Submonoid.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

/-- A finitely generated submonoid has a minimal generating set. -/
@[to_additive /-- A finitely generated submonoid has a minimal generating set. -/]
/-
**Submonoid.FG.exists_minimal_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.FG.exists_minimal_closure_eq (hP : P.FG) : exists S : Finset M, 
Minimal (fun S : Finset M => closure S = P) S
参数：hP : P.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_minimal_of_wellFoundedLT`：exists_minimal_of_wellFoundedLT (P : α 
-> Prop) (hP : exists a, P a) : exists a, Minimal P a

--- 原说明 ---
A finitely generated submonoid has a minimal generating set.
-/
lemma Submonoid.FG.exists_minimal_closure_eq (hP : P.FG) :
    ∃ S : Finset M, Minimal (fun S : Finset M ↦ closure S = P) S :=
  exists_minimal_of_wellFoundedLT _ hP
/-
**Submonoid.fg_iff_add_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.fg_iff_add_fg (P : Submonoid M) : P.FG ↔ P.toAddSubmonoid.FG
参数：P : Submonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.fg_iff`：Submonoid.fg_iff (P : Submonoid M) : Submonoid.FG P ↔ 
exists S : Set M, Submonoid.closure S = P ∧ S.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoid.fg_iff`：∀ {M : Type u_1} [inst : AddMonoid M] (P : AddSubmo
noid M), P.FG ↔ ∃ S, AddSubmonoid.closure S = P ∧ S.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem Submonoid.fg_iff_add_fg (P : Submonoid M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun h =>
    let ⟨S, hS, hf⟩ := (Submonoid.fg_iff _).1 h
    (AddSubmonoid.fg_iff _).mpr
      ⟨Additive.toMul ⁻¹' S, by simp [← Submonoid.toAddSubmonoid_closure, hS], hf⟩,
    fun h =>
    let ⟨T, hT, hf⟩ := (AddSubmonoid.fg_iff _).1 h
    (Submonoid.fg_iff _).mpr
      ⟨Additive.ofMul ⁻¹' T, by simp [← AddSubmonoid.toSubmonoid'_closure, hT], hf⟩⟩
/-
**AddSubmonoid.fg_iff_mul_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] (P : AddSubmonoid M) 
: P.FG ↔ P.toSubmonoid.FG
参数：P : AddSubmonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Submonoid.fg_iff_add_fg`：Submonoid.fg_iff_add_fg (P : Submonoid M) : P.F
G ↔ P.toAddSubmonoid.FG
-/
theorem AddSubmonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] (P : AddSubmonoid M) :
    P.FG ↔ P.toSubmonoid.FG := by
  convert! (Submonoid.fg_iff_add_fg (toSubmonoid P)).symm

@[to_additive]
/-
**Submonoid.FG.bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.bot : FG (⊥ : Submonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Submonoid.closure_empty`：closure_empty : closure (∅ : Set M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submonoid.FG.bot : FG (⊥ : Submonoid M) :=
  ⟨∅, by simp⟩

@[to_additive]
/-
**Submonoid.FG.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.sup {Q : Submonoid M} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG
参数：hP : P.FG；hQ : Q.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Submonoid.closure_union`：closure_union (s t : Set M) : closure (s union 
t) = closure s ⊔ closure t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submonoid.FG.sup {Q : Submonoid M} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s ∪ t, by simp [closure_union]⟩

@[to_additive]
/-
**Submonoid.FG.finset_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.finset_sup {ι : Type*} (s : Finset ι) (P : ι -> Submonoid M) 
(hP : forall i in s, (P i).FG) : (s.sup P).FG
参数：s : Finset ι；P : ι -> Submonoid M；hP : forall i in s, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_induction`：sup_induction {p : α -> Prop} (hb : p ⊥) (hp : for
all a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂)) (hs : forall b in s, p (f b)) : 
p (s.sup f…
· 使用定理 `Submonoid.FG.bot`：Submonoid.FG.bot : FG (⊥ : Submonoid M)
· 使用定理 `Submonoid.FG.sup`：Submonoid.FG.sup {Q : Submonoid M} (hP : P.FG) (hQ : Q
.FG) : (P ⊔ Q).FG
-/
theorem Submonoid.FG.finset_sup {ι : Type*} (s : Finset ι) (P : ι → Submonoid M)
    (hP : ∀ i ∈ s, (P i).FG) : (s.sup P).FG :=
  Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]
/-
**Submonoid.FG.biSup_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.biSup_finset {ι : Type*} (s : Finset ι) (P : ι -> Submonoid M
) (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG
参数：s : Finset ι；P : ι -> Submonoid M；hP : forall i in s, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `Submonoid.FG.finset_sup`：Submonoid.FG.finset_sup {ι : Type*} (s : Finset
 ι) (P : ι -> Submonoid M) (hP : forall i in s, (P i).FG) : (s.sup P).FG
-/
theorem Submonoid.FG.biSup_finset {ι : Type*} (s : Finset ι) (P : ι → Submonoid M)
    (hP : ∀ i ∈ s, (P i).FG) : (⨆ i ∈ s, P i).FG := by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]
/-
**Submonoid.FG.biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι -> Submo
noid M) (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG
参数：hs : s.Finite；P : ι -> Submonoid M；hP : forall i in s, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Submonoid.FG.biSup_finset`：Submonoid.FG.biSup_finset {ι : Type*} (s : Fi
nset ι) (P : ι -> Submonoid M) (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).
FG
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem Submonoid.FG.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι → Submonoid M)
    (hP : ∀ i ∈ s, (P i).FG) : (⨆ i ∈ s, P i).FG := by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]
/-
**Submonoid.FG.iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.iSup {ι : Sort*} [Finite ι] (P : ι -> Submonoid M) (hP : fora
ll i, (P i).FG) : (iSup P).FG
参数：P : ι -> Submonoid M；hP : forall i, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iSup_plift_down`：iSup_plift_down (f : ι -> α) : ⨆ i, f (PLift.down i) = 
⨆ i, f i
· 使用定理 `Submonoid.FG.biSup`：Submonoid.FG.biSup {ι : Type*} {s : Set ι} (hs : s.F
inite) (P : ι -> Submonoid M) (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).F
G
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `instFinitePLift`：∀ {α : Sort u_1} [Finite α], Finite (PLift α)
-/
theorem Submonoid.FG.iSup {ι : Sort*} [Finite ι] (P : ι → Submonoid M) (hP : ∀ i, (P i).FG) :
    (iSup P).FG := by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

/-- The product of two finitely generated submonoids is finitely generated. -/
@[to_additive prod
/-- The product of two finitely generated additive submonoids is finitely generated. -/]
/-
**Submonoid.FG.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.prod (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG
参数：hP : P.FG；hQ : Q.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submonoid.closure_union`：closure_union (s t : Set M) : closure (s union 
t) = closure s ⊔ closure t
· 使用引理 `Submonoid.closure_prod_one`：closure_prod_one (s : Set M) : closure (s ×ˢ
 ({1} : Set N)) = (closure s).prod ⊥
· 使用引理 `Submonoid.closure_one_prod`：closure_one_prod (t : Set N) : closure (({1}
 : Set M) ×ˢ t) = .prod ⊥ (closure t)
· 使用定理 `Submonoid.prod_bot_sup_bot_prod`：prod_bot_sup_bot_prod (s : Submonoid M)
 (t : Submonoid N) : (prod s ⊥) ⊔ (prod ⊥ t) = prod s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submonoid.FG.prod (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG := by
  classical
  obtain ⟨bM, hbM⟩ := hP
  obtain ⟨bN, hbN⟩ := hQ
  refine ⟨bM ×ˢ singleton 1 ∪ singleton 1 ×ˢ bN, ?_⟩
  push_cast
  simp [closure_union, hbM, hbN]

section Pi

variable {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, Monoid (M i)] {P : ∀ i, Submonoid (M i)}

@[to_additive]
/-
**Submonoid.iSup_map_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.iSup_map_mulSingle [DecidableEq ι] : ⨆ i, map (MonoidHom.mulSing
le M i) (P i) = pi Set.univ P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submonoid.iSup_map_mulSingle_le`：iSup_map_mulSingle_le [DecidableEq ι] {
I : Set ι} {S : forall i, Submonoid (M i)} : ⨆ i, map (MonoidHom.mulSingle M i) 
(S i) <= pi I S
· 使用定理 `Pi.mulSingle_apply_commute`：Pi.mulSingle_apply_commute [forall i, MulOne
Class <| f i] (x : forall i, f i) (i j : I) : Commute (mulSingle i (x i)) (mulSi
ngle j (x j))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.noncommProd_mulSingle`：noncommProd_mulSingle [Fintype ι] [Decidab
leEq ι] (x : forall i, M i) : (univ.noncommProd (fun i => Pi.mulSingle i (x i)) 
fun i _ j _ _ => P…
· 使用定理 `Submonoid.noncommProd_mem`：noncommProd_mem (S : Submonoid M) {ι : Type*}
 (t : Finset ι) (f : ι -> M) (comm) (h : forall c in t, f c in S) : t.noncommPro
d f comm in S
· 使用定理 `Submonoid.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {S : ι -> Submono
id M} (i : ι) : forall {x : M}, x in S i -> x in iSup S
· 使用定理 `Submonoid.mem_map_of_mem`：mem_map_of_mem (f : F) {S : Submonoid M} {x : 
M} (hx : x in S) : f x in S.map f
· 使用定理 `trivial`：True
-/
theorem Submonoid.iSup_map_mulSingle [DecidableEq ι] :
    ⨆ i, map (MonoidHom.mulSingle M i) (P i) = pi Set.univ P := by
  have := Fintype.ofFinite ι
  refine iSup_map_mulSingle_le.antisymm fun x hx => ?_
  rw [← Finset.noncommProd_mulSingle x]
  exact noncommProd_mem _ _ _ _ fun i _ => mem_iSup_of_mem _ (mem_map_of_mem _ (hx i trivial))

/-- Finite product of finitely generated submonoids is finitely generated. -/
@[to_additive
/-- Finite product of finitely generated additive submonoids is finitely generated. -/]
/-
**Submonoid.FG.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.pi (hP : forall i, (P i).FG) : (pi Set.univ P).FG
参数：hP : forall i, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.biUnion_univ`：biUnion_univ (s : α -> Set β) : ⋃ x in @univ α, s x = 
⋃ x, s x
· 使用定理 `Submonoid.closure_iUnion`：closure_iUnion {ι} (s : ι -> Set M) : closure 
(⋃ i, s i) = ⨆ i, closure (s i)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Submonoid.map.congr_simp`：∀ {M : Type u_1} {N : Type u_2} [inst : MulOne
Class M] [inst_1 : MulOneClass N] {F : Type u_4} [inst_2 : FunLike F M N]   [mc 
: MonoidHomCla…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.iSup_map_mulSingle`：Submonoid.iSup_map_mulSingle [DecidableEq 
ι] : ⨆ i, map (MonoidHom.mulSingle M i) (P i) = pi Set.univ P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Submonoid.FG.pi (hP : ∀ i, (P i).FG) : (pi Set.univ P).FG := by
  classical
  have := Fintype.ofFinite ι
  choose s hs using hP
  refine ⟨Finset.univ.biUnion fun i => (s i).image (MonoidHom.mulSingle M i), ?_⟩
  simp_rw [Finset.coe_biUnion, Finset.coe_univ, Set.biUnion_univ, closure_iUnion, Finset.coe_image,
    ← MonoidHom.map_mclosure, hs, iSup_map_mulSingle]

end Pi

end Submonoid

section Monoid

/-- An additive monoid is finitely generated if it is finitely generated as an additive submonoid of
itself. -/
@[mk_iff]
/-
**AddMonoid.FG** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddMonoid`。
形式化陈述：(M : Type u_3) → [AddMonoid M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive monoid is finitely generated if it is finitely generated as an addit
ive submonoid of
itself.
-/
class AddMonoid.FG (M : Type*) [AddMonoid M] : Prop where
  fg_top : (⊤ : AddSubmonoid M).FG

variable (M) in
/-- A monoid is finitely generated if it is finitely generated as a submonoid of itself. -/
@[to_additive]
/-
**Monoid.FG** 是 Mathlib 中的一个归纳类型，位于命名空间 `Monoid`。
形式化陈述：(M : Type u_1) → [Monoid M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoid is finitely generated if it is finitely generated as a submonoid of its
elf.
-/
class Monoid.FG : Prop where
  fg_top : (⊤ : Submonoid M).FG

@[to_additive]
/-
**Monoid.fg_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.FG.fg_top`：∀ {M : Type u_1} {inst : Monoid M} [self : Monoid.FG M
], ⊤.FG
-/
theorem Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Monoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddMonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/]
/-
**Monoid.fg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.fg_iff : Monoid.FG M ↔ exists S : Set M, Submonoid.closure S = (⊤ :
 Submonoid M) ∧ S.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.fg_iff`：Submonoid.fg_iff (P : Submonoid M) : Submonoid.FG P ↔ 
exists S : Set M, Submonoid.closure S = P ∧ S.Finite
· 使用定理 `Monoid.FG.fg_top`：∀ {M : Type u_1} {inst : Monoid M} [self : Monoid.FG M
], ⊤.FG
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem Monoid.fg_iff :
    Monoid.FG M ↔ ∃ S : Set M, Submonoid.closure S = (⊤ : Submonoid M) ∧ S.Finite :=
  ⟨fun _ => (Submonoid.fg_iff ⊤).1 FG.fg_top, fun h => ⟨(Submonoid.fg_iff ⊤).2 h⟩⟩

variable (M) in
/-- A finitely generated monoid has a minimal generating set. -/
@[to_additive /-- A finitely generated monoid has a minimal generating set. -/]
/-
**Submonoid.exists_minimal_closure_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.exists_minimal_closure_eq_top [Monoid.FG M] : exists S : Finset 
M, Minimal (fun S => Submonoid.closure (SetLike.coe S) = ⊤) S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submonoid.FG.exists_minimal_closure_eq`：Submonoid.FG.exists_minimal_clos
ure_eq (hP : P.FG) : exists S : Finset M, Minimal (fun S : Finset M => closure S
 = P) S
· 使用定理 `Monoid.FG.fg_top`：∀ {M : Type u_1} {inst : Monoid M} [self : Monoid.FG M
], ⊤.FG

--- 原说明 ---
A finitely generated monoid has a minimal generating set.
-/
lemma Submonoid.exists_minimal_closure_eq_top [Monoid.FG M] :
    ∃ S : Finset M, Minimal (fun S ↦ Submonoid.closure (SetLike.coe S) = ⊤) S :=
  Monoid.FG.fg_top.exists_minimal_closure_eq
/-
**Monoid.fg_iff_add_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG (Additive M) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.fg_iff_add_fg`：Submonoid.fg_iff_add_fg (P : Submonoid M) : P.F
G ↔ P.toAddSubmonoid.FG
· 使用定理 `Monoid.FG.fg_top`：∀ {M : Type u_1} {inst : Monoid M} [self : Monoid.FG M
], ⊤.FG
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddMonoid.FG.fg_top`：∀ {M : Type u_3} {inst : AddMonoid M} [self : AddMo
noid.FG M], ⊤.FG
-/
theorem Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG (Additive M) where
  mp _ := ⟨(Submonoid.fg_iff_add_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(Submonoid.fg_iff_add_fg ⊤).2 h.fg_top⟩
/-
**AddMonoid.fg_iff_mul_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] : AddMonoid.FG M ↔ Monoi
d.FG (Multiplicative M) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubmonoid.fg_iff_mul_fg`：AddSubmonoid.fg_iff_mul_fg {M : Type*} [AddM
onoid M] (P : AddSubmonoid M) : P.FG ↔ P.toSubmonoid.FG
· 使用定理 `AddMonoid.FG.fg_top`：∀ {M : Type u_3} {inst : AddMonoid M} [self : AddMo
noid.FG M], ⊤.FG
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.FG.fg_top`：∀ {M : Type u_1} {inst : Monoid M} [self : Monoid.FG M
], ⊤.FG
-/
theorem AddMonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] :
    AddMonoid.FG M ↔ Monoid.FG (Multiplicative M) where
  mp _ := ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).2 h.fg_top⟩
/-
**AddMonoid.fg_of_monoid_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.fg_of_monoid_fg [Monoid.FG M] : AddMonoid.FG (Additive M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Monoid.fg_iff_add_fg`：Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG 
(Additive M) where mp _
-/
instance AddMonoid.fg_of_monoid_fg [Monoid.FG M] : AddMonoid.FG (Additive M) :=
  Monoid.fg_iff_add_fg.1 ‹_›
/-
**Monoid.fg_of_addMonoid_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.fg_of_addMonoid_fg {M : Type*} [AddMonoid M] [AddMonoid.FG M] : Mon
oid.FG (Multiplicative M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoid.fg_iff_mul_fg`：AddMonoid.fg_iff_mul_fg {M : Type*} [AddMonoid 
M] : AddMonoid.FG M ↔ Monoid.FG (Multiplicative M) where mp _
-/
instance Monoid.fg_of_addMonoid_fg {M : Type*} [AddMonoid M] [AddMonoid.FG M] :
    Monoid.FG (Multiplicative M) :=
  AddMonoid.fg_iff_mul_fg.1 ‹_›

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
@[to_additive]
/-
**Monoid.fg_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monoid.fg_of_finite [Finite M] : Monoid.FG M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Submonoid.closure_univ`：closure_univ : closure (univ : Set M) = ⊤
-/
lemma Monoid.fg_of_finite [Finite M] : Monoid.FG M := by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Submonoid.closure_univ⟩⟩

end Monoid

@[to_additive]
/-
**Submonoid.FG.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.map {M' : Type*} [Monoid M'] {P : Submonoid M} (h : P.FG) (e 
: M ->* M') : (P.map e).FG
参数：h : P.FG；e : M ->* M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `MonoidHom.map_mclosure`：map_mclosure (f : F) (s : Set M) : (closure s).m
ap f = closure (f '' s)
-/
theorem Submonoid.FG.map {M' : Type*} [Monoid M'] {P : Submonoid M} (h : P.FG) (e : M →* M') :
    (P.map e).FG := by
  classical
    obtain ⟨s, rfl⟩ := h
    exact ⟨s.image e, by rw [Finset.coe_image, MonoidHom.map_mclosure]⟩

@[to_additive]
/-
**Submonoid.FG.map_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.FG.map_injective {M' : Type*} [Monoid M'] {P : Submonoid M} (e :
 M ->* M') (he : Function.Injective e) (h : (P.map e).FG) : P.FG
参数：e : M ->* M'；he : Function.Injective e；h : (P.map e).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Submonoid.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_mclosure`：map_mclosure (f : F) (s : Set M) : (closure s).m
ap f = closure (f '' s)
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `MonoidHom.coe_mrange`：coe_mrange (f : F) : (mrange f : Set N) = Set.rang
e f
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `Submonoid.monotone_map`：monotone_map {f : F} : Monotone (map f)
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem Submonoid.FG.map_injective {M' : Type*} [Monoid M'] {P : Submonoid M} (e : M →* M')
    (he : Function.Injective e) (h : (P.map e).FG) : P.FG := by
  obtain ⟨s, hs⟩ := h
  use s.preimage e he.injOn
  apply Submonoid.map_injective_of_injective he
  rw [← hs, MonoidHom.map_mclosure e, Finset.coe_preimage]
  congr
  rw [Set.image_preimage_eq_iff, ← MonoidHom.coe_mrange e, ← Submonoid.closure_le, hs,
      MonoidHom.mrange_eq_map e]
  exact Submonoid.monotone_map le_top

@[to_additive (attr := simp)]
/-
**Monoid.fg_iff_submonoid_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.fg_iff_submonoid_fg (N : Submonoid M) : Monoid.FG N ↔ N.FG
参数：N : Submonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.mrange_subtype`：mrange_subtype (s : Submonoid M) : mrange s.su
btype = s
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `Submonoid.FG.map`：Submonoid.FG.map {M' : Type*} [Monoid M'] {P : Submono
id M} (h : P.FG) (e : M ->* M') : (P.map e).FG
· 使用定理 `Monoid.FG.fg_top`：∀ {M : Type u_1} {inst : Monoid M} [self : Monoid.FG M
], ⊤.FG
· 使用定理 `Submonoid.FG.map_injective`：Submonoid.FG.map_injective {M' : Type*} [Mon
oid M'] {P : Submonoid M} (e : M ->* M') (he : Function.Injective e) (h : (P.map
 e).FG) : P.FG
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem Monoid.fg_iff_submonoid_fg (N : Submonoid M) : Monoid.FG N ↔ N.FG := by
  conv_rhs => rw [← N.mrange_subtype, MonoidHom.mrange_eq_map]
  exact ⟨fun h ↦ h.fg_top.map N.subtype, fun h => ⟨h.map_injective N.subtype Subtype.coe_injective⟩⟩

@[to_additive]
/-
**Monoid.fg_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.fg_of_surjective {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M ->* 
M') (hf : Function.Surjective f) : Monoid.FG M'
参数：f : M ->* M'；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Monoid.fg_def`：Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_mclosure`：map_mclosure (f : F) (s : Set M) : (closure s).m
ap f = closure (f '' s)
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `MonoidHom.mrange_eq_top`：mrange_eq_top {f : F} : mrange f = (⊤ : Submono
id N) ↔ Surjective f
-/
theorem Monoid.fg_of_surjective {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M →* M')
    (hf : Function.Surjective f) : Monoid.FG M' := by
  classical
    obtain ⟨s, hs⟩ := Monoid.fg_def.mp ‹_›
    use s.image f
    rwa [Finset.coe_image, ← MonoidHom.map_mclosure, hs, ← MonoidHom.mrange_eq_map,
      MonoidHom.mrange_eq_top]

@[to_additive]
/-
**Monoid.fg_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.fg_range {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M ->* M') : Mo
noid.FG (MonoidHom.mrange f)
参数：f : M ->* M'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.fg_of_surjective`：Monoid.fg_of_surjective {M' : Type*} [Monoid M'
] [Monoid.FG M] (f : M ->* M') (hf : Function.Surjective f) : Monoid.FG M'
· 使用定理 `MonoidHom.mrangeRestrict_surjective`：mrangeRestrict_surjective (f : M ->
* N) : Function.Surjective f.mrangeRestrict
-/
instance Monoid.fg_range {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M →* M') :
    Monoid.FG (MonoidHom.mrange f) :=
  Monoid.fg_of_surjective f.mrangeRestrict f.mrangeRestrict_surjective

open FreeMonoid in
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Finite α] : Monoid.FG (FreeMonoid α) :=
  Monoid.fg_iff.mpr ⟨Set.range of, closure_range_of, Set.finite_range of⟩

/-- A monoid is finitely generated iff there exists a surjective homomorphism from a `FreeMonoid`
on finitely many generators. -/
@[to_additive /-- An additive monoid is finitely generated iff there exists a surjective
homomorphism from a `FreeAddMonoid` on finitely many generators.-/]
/-
**Monoid.fg_iff_exists_freeMonoid_hom_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.fg_iff_exists_freeMonoid_hom_surjective : Monoid.FG M ↔ exists (S :
 Set M) (_ : S.Finite) (φ : FreeMonoid S ->* M), Function.Surjective φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.mrange_eq_top`：mrange_eq_top {f : F} : mrange f = (⊤ : Submono
id N) ↔ Surjective f
· 使用定理 `Submonoid.closure_eq_mrange`：closure_eq_mrange (s : Set M) : closure s =
 mrange (FreeMonoid.lift ((↑) : s -> M))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.fg_iff`：Monoid.fg_iff : Monoid.FG M ↔ exists S : Set M, Submonoid
.closure S = (⊤ : Submonoid M) ∧ S.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submonoid.map.congr_simp`：∀ {M : Type u_1} {N : Type u_2} [inst : MulOne
Class M] [inst_1 : MulOneClass N] {F : Type u_4} [inst_2 : FunLike F M N]   [mc 
: MonoidHomCla…
· 使用定理 `FreeMonoid.closure_range_of`：closure_range_of : closure (Set.range <| @o
f α) = ⊤
· 使用定理 `MonoidHom.mrange_eq_top_of_surjective`：mrange_eq_top_of_surjective (f : 
F) (hf : Function.Surjective f) : mrange f = (⊤ : Submonoid N)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem Monoid.fg_iff_exists_freeMonoid_hom_surjective :
    Monoid.FG M ↔ ∃ (S : Set M) (_ : S.Finite) (φ : FreeMonoid S →* M), Function.Surjective φ := by
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨S, S.finite_toSet, FreeMonoid.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.mrange_eq_top, ← Submonoid.closure_eq_mrange]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    refine fg_iff.mpr ⟨φ '' Set.range FreeMonoid.of, ?_, Set.toFinite _⟩
    simp [← MonoidHom.map_mclosure, hφ, FreeMonoid.closure_range_of, ← MonoidHom.mrange_eq_map]

/-- A monoid if finitely generated if and only if there exists a surjective homomorphism from a
`FreeMonoid` on an arbitrary finite type `α` to the monoid. -/
@[to_additive /-- An additive monoid is finitely generated iff there exists a surjective
homomorphism from a `FreeAddMonoid` on an arbitrary finite type `α` to the monoid. -/]
/-
**Monoid.fg_iff_exists_freeGroup_hom_surjective_finite** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Monoid.fg_iff_exists_freeGroup_hom_surjective_finite : Monoid.FG M ↔ exist
s (α : Type) (_ : Finite α) (φ : FreeMonoid α ->* M), Function.Surjective φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.fg_iff_exists_freeMonoid_hom_surjective`：Monoid.fg_iff_exists_fre
eMonoid_hom_surjective : Monoid.FG M ↔ exists (S : Set M) (_ : S.Finite) (φ : Fr
eeMonoid S ->* M), Function.Surjecti…
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `Monoid.fg_of_surjective`：Monoid.fg_of_surjective {M' : Type*} [Monoid M'
] [Monoid.FG M] (f : M ->* M') (hf : Function.Surjective f) : Monoid.FG M'
· 使用定理 `instFGFreeMonoidOfFinite`：∀ (α : Type u_3) [Finite α], Monoid.FG (FreeMo
noid α)
-/
theorem Monoid.fg_iff_exists_freeGroup_hom_surjective_finite :
    Monoid.FG M ↔ ∃ (α : Type) (_ : Finite α) (φ : FreeMonoid α →* M), Function.Surjective φ := by
  constructor
  · rw [fg_iff_exists_freeMonoid_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeMonoid.freeMonoidCongr e).symm,
      hφ.comp (FreeMonoid.freeMonoidCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Monoid.fg_of_surjective _ hφ

@[to_additive]
/-
**Submonoid.powers_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.powers_fg (r : M) : (Submonoid.powers r).FG
参数：r : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.powers_eq_closure`：powers_eq_closure (n : M) : powers n = clos
ure {n}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
-/
theorem Submonoid.powers_fg (r : M) : (Submonoid.powers r).FG :=
  ⟨{r}, (Finset.coe_singleton r).symm ▸ (Submonoid.powers_eq_closure r).symm⟩

@[to_additive]
/-
**Monoid.powers_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.powers_fg (r : M) : Monoid.FG (Submonoid.powers r)
参数：r : M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.fg_iff_submonoid_fg`：Monoid.fg_iff_submonoid_fg (N : Submonoid M)
 : Monoid.FG N ↔ N.FG
· 使用定理 `Submonoid.powers_fg`：Submonoid.powers_fg (r : M) : (Submonoid.powers r).
FG
-/
instance Monoid.powers_fg (r : M) : Monoid.FG (Submonoid.powers r) :=
  (Monoid.fg_iff_submonoid_fg _).mpr (Submonoid.powers_fg r)

@[to_additive]
/-
**Monoid.closure_finset_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.closure_finset_fg (s : Finset M) : Monoid.FG (Submonoid.closure (s 
: Set M))
参数：s : Finset M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Submonoid.closure_closure_coe_preimage`：closure_closure_coe_preimage {s 
: Set M} : closure (((↑) : closure s -> M) ⁻¹' s) = ⊤
-/
instance Monoid.closure_finset_fg (s : Finset M) : Monoid.FG (Submonoid.closure (s : Set M)) := by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage, Submonoid.closure_closure_coe_preimage]

@[to_additive]
/-
**Monoid.closure_finite_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.closure_finite_fg (s : Set M) [Finite s] : Monoid.FG (Submonoid.clo
sure s)
参数：s : Set M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
-/
instance Monoid.closure_finite_fg (s : Set M) [Finite s] : Monoid.FG (Submonoid.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Monoid.closure_finset_fg s.toFinset

/-! ### Groups and subgroups -/


variable {G H : Type*} [Group G] [AddGroup H]

section Subgroup

/-- A subgroup of `G` is finitely generated if it is the closure of a finite subset of `G`. -/
@[to_additive]
/-
**Subgroup.FG** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.FG (P : Subgroup G) : Prop
参数：P : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of `G` is finitely generated if it is the closure of a finite subset 
of `G`.
-/
def Subgroup.FG (P : Subgroup G) : Prop :=
  ∃ S : Finset G, Subgroup.closure ↑S = P

/-- An additive subgroup of `H` is finitely generated if it is the closure of a finite subset of
`H`. -/
add_decl_doc AddSubgroup.FG

/-- An equivalent expression of `Subgroup.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubgroup.fg` in terms of `Set.Finite` instead of
`Finset`. -/]
/-
**Subgroup.fg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.fg_iff (P : Subgroup G) : Subgroup.FG P ↔ exists S : Set G, Subgr
oup.closure S = P ∧ S.Finite
参数：P : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Subgroup.fg_iff (P : Subgroup G) :
    Subgroup.FG P ↔ ∃ S : Set G, Subgroup.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

/-- A subgroup is finitely generated if and only if it is finitely generated as a submonoid. -/
@[to_additive /-- An additive subgroup is finitely generated if
and only if it is finitely generated as an additive submonoid. -/]
/-
**Subgroup.fg_iff_submonoid_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.fg_iff_submonoid_fg (P : Subgroup G) : P.FG ↔ P.toSubmonoid.FG
参数：P : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.fg_iff`：Submonoid.fg_iff (P : Submonoid M) : Submonoid.FG P ↔ 
exists S : Set M, Submonoid.closure S = P ∧ S.Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.closure_toSubmonoid`：closure_toSubmonoid (S : Set G) : (closure
 S).toSubmonoid = Submonoid.closure (S union S⁻¹)
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.Finite.inv`：∀ {α : Type u_2} [inst : InvolutiveInv α] {s : Set α}, s
.Finite → s⁻¹.Finite
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `Subgroup.coe_toSubmonoid`：coe_toSubmonoid (K : Subgroup G) : (K.toSubmon
oid : Set G) = K
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Subgroup.toSubmonoid_le`：toSubmonoid_le {p q : Subgroup G} : p.toSubmono
id <= q.toSubmonoid ↔ p <= q
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
-/
theorem Subgroup.fg_iff_submonoid_fg (P : Subgroup G) : P.FG ↔ P.toSubmonoid.FG := by
  constructor
  · rintro ⟨S, rfl⟩
    rw [Submonoid.fg_iff]
    refine ⟨S ∪ S⁻¹, ?_, S.finite_toSet.union S.finite_toSet.inv⟩
    exact (Subgroup.closure_toSubmonoid _).symm
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le, ← Subgroup.coe_toSubmonoid, ← hS]
      exact Submonoid.subset_closure
    · rw [← Subgroup.toSubmonoid_le, ← hS, Submonoid.closure_le]
      exact Subgroup.subset_closure
/-
**Subgroup.fg_iff_add_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.fg_iff_add_fg (P : Subgroup G) : P.FG ↔ P.toAddSubgroup.FG
参数：P : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.fg_iff_submonoid_fg`：Subgroup.fg_iff_submonoid_fg (P : Subgroup
 G) : P.FG ↔ P.toSubmonoid.FG
· 使用定理 `AddSubgroup.fg_iff_addSubmonoid_fg`：∀ {G : Type u_3} [inst : AddGroup G]
 (P : AddSubgroup G), P.FG ↔ P.FG
· 使用定理 `Submonoid.fg_iff_add_fg`：Submonoid.fg_iff_add_fg (P : Submonoid M) : P.F
G ↔ P.toAddSubmonoid.FG
-/
theorem Subgroup.fg_iff_add_fg (P : Subgroup G) : P.FG ↔ P.toAddSubgroup.FG := by
  rw [Subgroup.fg_iff_submonoid_fg, AddSubgroup.fg_iff_addSubmonoid_fg]
  exact (Subgroup.toSubmonoid P).fg_iff_add_fg
/-
**AddSubgroup.fg_iff_mul_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubgroup.fg_iff_mul_fg (P : AddSubgroup H) : P.FG ↔ P.toSubgroup.FG
参数：P : AddSubgroup H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.fg_iff_addSubmonoid_fg`：∀ {G : Type u_3} [inst : AddGroup G]
 (P : AddSubgroup G), P.FG ↔ P.FG
· 使用定理 `Subgroup.fg_iff_submonoid_fg`：Subgroup.fg_iff_submonoid_fg (P : Subgroup
 G) : P.FG ↔ P.toSubmonoid.FG
· 使用定理 `AddSubmonoid.fg_iff_mul_fg`：AddSubmonoid.fg_iff_mul_fg {M : Type*} [AddM
onoid M] (P : AddSubmonoid M) : P.FG ↔ P.toSubmonoid.FG
-/
theorem AddSubgroup.fg_iff_mul_fg (P : AddSubgroup H) : P.FG ↔ P.toSubgroup.FG := by
  rw [AddSubgroup.fg_iff_addSubmonoid_fg, Subgroup.fg_iff_submonoid_fg]
  exact AddSubmonoid.fg_iff_mul_fg (AddSubgroup.toAddSubmonoid P)

@[to_additive]
/-
**Subgroup.FG.bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.FG.bot : FG (⊥ : Subgroup G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Subgroup.closure_empty`：closure_empty : closure (∅ : Set G) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Subgroup.FG.bot : FG (⊥ : Subgroup G) :=
  ⟨∅, by simp⟩

@[to_additive]
/-
**Subgroup.FG.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.FG.sup {P Q : Subgroup G} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG
参数：hP : P.FG；hQ : Q.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Subgroup.closure_union`：closure_union (s t : Set G) : closure (s union t
) = closure s ⊔ closure t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Subgroup.FG.sup {P Q : Subgroup G} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s ∪ t, by simp [closure_union]⟩

@[to_additive]
/-
**Subgroup.FG.finset_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.FG.finset_sup {ι : Type*} (s : Finset ι) (P : ι -> Subgroup G) (h
P : forall i in s, (P i).FG) : (s.sup P).FG
参数：s : Finset ι；P : ι -> Subgroup G；hP : forall i in s, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_induction`：sup_induction {p : α -> Prop} (hb : p ⊥) (hp : for
all a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂)) (hs : forall b in s, p (f b)) : 
p (s.sup f…
· 使用定理 `Subgroup.FG.bot`：Subgroup.FG.bot : FG (⊥ : Subgroup G)
· 使用定理 `Subgroup.FG.sup`：Subgroup.FG.sup {P Q : Subgroup G} (hP : P.FG) (hQ : Q.
FG) : (P ⊔ Q).FG
-/
theorem Subgroup.FG.finset_sup {ι : Type*} (s : Finset ι) (P : ι → Subgroup G)
    (hP : ∀ i ∈ s, (P i).FG) : (s.sup P).FG :=
  Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]
/-
**Subgroup.FG.biSup_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.FG.biSup_finset {ι : Type*} (s : Finset ι) (P : ι -> Subgroup G) 
(hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG
参数：s : Finset ι；P : ι -> Subgroup G；hP : forall i in s, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `Subgroup.FG.finset_sup`：Subgroup.FG.finset_sup {ι : Type*} (s : Finset ι
) (P : ι -> Subgroup G) (hP : forall i in s, (P i).FG) : (s.sup P).FG
-/
theorem Subgroup.FG.biSup_finset {ι : Type*} (s : Finset ι) (P : ι → Subgroup G)
    (hP : ∀ i ∈ s, (P i).FG) : (⨆ i ∈ s, P i).FG := by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]
/-
**Subgroup.FG.biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.FG.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι -> Subgro
up G) (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG
参数：hs : s.Finite；P : ι -> Subgroup G；hP : forall i in s, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subgroup.FG.biSup_finset`：Subgroup.FG.biSup_finset {ι : Type*} (s : Fins
et ι) (P : ι -> Subgroup G) (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem Subgroup.FG.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι → Subgroup G)
    (hP : ∀ i ∈ s, (P i).FG) : (⨆ i ∈ s, P i).FG := by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]
/-
**Subgroup.FG.iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.FG.iSup {ι : Sort*} [Finite ι] (P : ι -> Subgroup G) (hP : forall
 i, (P i).FG) : (iSup P).FG
参数：P : ι -> Subgroup G；hP : forall i, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iSup_plift_down`：iSup_plift_down (f : ι -> α) : ⨆ i, f (PLift.down i) = 
⨆ i, f i
· 使用定理 `Subgroup.FG.biSup`：Subgroup.FG.biSup {ι : Type*} {s : Set ι} (hs : s.Fin
ite) (P : ι -> Subgroup G) (hP : forall i in s, (P i).FG) : (⨆ i in s, P i).FG
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `instFinitePLift`：∀ {α : Sort u_1} [Finite α], Finite (PLift α)
-/
theorem Subgroup.FG.iSup {ι : Sort*} [Finite ι] (P : ι → Subgroup G) (hP : ∀ i, (P i).FG) :
    (iSup P).FG := by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

/-- The product of two finitely generated subgroups is finitely generated. -/
@[to_additive prod
/-- The product of two finitely generated additive subgroups is finitely generated. -/]
/-
**Subgroup.FG.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.FG.prod {G' : Type*} [Group G'] {P : Subgroup G} {Q : Subgroup G'
} (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG
参数：hP : P.FG；hQ : Q.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.fg_iff_submonoid_fg`：Subgroup.fg_iff_submonoid_fg (P : Subgroup
 G) : P.FG ↔ P.toSubmonoid.FG
· 使用定理 `Submonoid.FG.prod`：Submonoid.FG.prod (hP : P.FG) (hQ : Q.FG) : (P.prod Q
).FG
-/
theorem Subgroup.FG.prod {G' : Type*} [Group G'] {P : Subgroup G} {Q : Subgroup G'}
    (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG := by
  rw [fg_iff_submonoid_fg] at *
  exact hP.prod hQ

/-- Finite product of finitely generated subgroups is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive subgroups is finitely generated. -/]
/-
**Subgroup.FG.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.FG.pi {ι : Type*} [Finite ι] {G : ι -> Type*} [forall i, Group (G
 i)] {P : forall i, Subgroup (G i)} (hP : forall i, (P i).FG) : (pi Set.univ P).
FG
参数：G i；G i；hP : forall i, (P i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.FG.pi`：Submonoid.FG.pi (hP : forall i, (P i).FG) : (pi Set.uni
v P).FG
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Finite product of finitely generated subgroups is finitely generated.
-/
theorem Subgroup.FG.pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    {P : ∀ i, Subgroup (G i)} (hP : ∀ i, (P i).FG) : (pi Set.univ P).FG := by
  simp_rw [fg_iff_submonoid_fg] at *
  exact .pi hP

end Subgroup

section Group

variable (G H)

/-- A group is finitely generated if it is finitely generated as a subgroup of itself. -/
/-
**Group.FG** 是 Mathlib 中的一个归纳类型，位于命名空间 `Group`。
形式化陈述：(G : Type u_3) → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group is finitely generated if it is finitely generated as a subgroup of itsel
f.
-/
class Group.FG : Prop where
  out : (⊤ : Subgroup G).FG

/-- An additive group is finitely generated if it is finitely generated as an additive subgroup of
itself. -/
/-
**AddGroup.FG** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddGroup`。
形式化陈述：(H : Type u_4) → [AddGroup H] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive group is finitely generated if it is finitely generated as an additi
ve subgroup of
itself.
-/
class AddGroup.FG : Prop where
  out : (⊤ : AddSubgroup H).FG

attribute [to_additive] Group.FG

variable {G H}
/-
**Group.fg_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.FG.out`：∀ {G : Type u_3} {inst : Group G} [self : Group.FG G], ⊤.F
G
-/
theorem Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
/-
**AddGroup.fg_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddGroup.fg_def : AddGroup.FG H ↔ (⊤ : AddSubgroup H).FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroup.FG.out`：∀ {H : Type u_4} {inst : AddGroup H} [self : AddGroup.F
G H], ⊤.FG
-/
theorem AddGroup.fg_def : AddGroup.FG H ↔ (⊤ : AddSubgroup H).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Group.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddGroup.fg` in terms of `Set.Finite` instead of `Finset`. -/]
/-
**Group.fg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.fg_iff : Group.FG G ↔ exists S : Set G, Subgroup.closure S = (⊤ : Su
bgroup G) ∧ S.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.fg_iff`：Subgroup.fg_iff (P : Subgroup G) : Subgroup.FG P ↔ exis
ts S : Set G, Subgroup.closure S = P ∧ S.Finite
· 使用定理 `Group.FG.out`：∀ {G : Type u_3} {inst : Group G} [self : Group.FG G], ⊤.F
G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem Group.fg_iff : Group.FG G ↔ ∃ S : Set G, Subgroup.closure S = (⊤ : Subgroup G) ∧ S.Finite :=
  ⟨fun h => (Subgroup.fg_iff ⊤).1 h.out, fun h => ⟨(Subgroup.fg_iff ⊤).2 h⟩⟩

@[to_additive]
/-
**Group.fg_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.fg_iff' : Group.FG G ↔ exists (n : _) (S : Finset G), S.card = n ∧ S
ubgroup.closure (S : Set G) = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Group.fg_def`：Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG
-/
theorem Group.fg_iff' :
    Group.FG G ↔ ∃ (n : _) (S : Finset G), S.card = n ∧ Subgroup.closure (S : Set G) = ⊤ :=
  Group.fg_def.trans ⟨fun ⟨S, hS⟩ => ⟨S.card, S, rfl, hS⟩, fun ⟨_n, S, _hn, hS⟩ => ⟨S, hS⟩⟩

/-- A group is finitely generated if and only if it is finitely generated as a monoid. -/
@[to_additive /-- An additive group is finitely generated if and only
if it is finitely generated as an additive monoid. -/]
/-
**Group.fg_iff_monoid_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.fg_def`：Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.fg_iff_submonoid_fg`：Subgroup.fg_iff_submonoid_fg (P : Subgroup
 G) : P.FG ↔ P.toSubmonoid.FG
· 使用定理 `Group.fg_def`：Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG
-/
theorem Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG G :=
  ⟨fun h => Monoid.fg_def.2 <| (Subgroup.fg_iff_submonoid_fg ⊤).1 (Group.fg_def.1 h), fun h =>
    Group.fg_def.2 <| (Subgroup.fg_iff_submonoid_fg ⊤).2 (Monoid.fg_def.1 h)⟩

@[to_additive]
/-
**Monoid.fg_of_group_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.fg_of_group_fg [Group.FG G] : Monoid.FG G
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.fg_iff_monoid_fg`：Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG 
G
-/
instance Monoid.fg_of_group_fg [Group.FG G] : Monoid.FG G :=
  Group.fg_iff_monoid_fg.1 ‹_›

@[to_additive (attr := simp)]
/-
**Group.fg_iff_subgroup_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.fg_iff_subgroup_fg (H : Subgroup G) : Group.FG H ↔ H.FG
参数：H : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Group.fg_iff_monoid_fg`：Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG 
G
· 使用定理 `Monoid.fg_iff_submonoid_fg`：Monoid.fg_iff_submonoid_fg (N : Submonoid M)
 : Monoid.FG N ↔ N.FG
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subgroup.fg_iff_submonoid_fg`：Subgroup.fg_iff_submonoid_fg (P : Subgroup
 G) : P.FG ↔ P.toSubmonoid.FG
-/
theorem Group.fg_iff_subgroup_fg (H : Subgroup G) : Group.FG H ↔ H.FG :=
  (fg_iff_monoid_fg.trans (Monoid.fg_iff_submonoid_fg _)).trans
    (Subgroup.fg_iff_submonoid_fg _).symm
/-
**GroupFG.iff_add_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Additive G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.fg_iff_add_fg`：Subgroup.fg_iff_add_fg (P : Subgroup G) : P.FG ↔
 P.toAddSubgroup.FG
· 使用定理 `Group.FG.out`：∀ {G : Type u_3} {inst : Group G} [self : Group.FG G], ⊤.F
G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddGroup.FG.out`：∀ {H : Type u_4} {inst : AddGroup H} [self : AddGroup.F
G H], ⊤.FG
-/
theorem GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Additive G) :=
  ⟨fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).1 h.out⟩, fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).2 h.out⟩⟩
/-
**AddGroup.fg_iff_mul_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddGroup.fg_iff_mul_fg : AddGroup.FG H ↔ Group.FG (Multiplicative H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubgroup.fg_iff_mul_fg`：AddSubgroup.fg_iff_mul_fg (P : AddSubgroup H)
 : P.FG ↔ P.toSubgroup.FG
· 使用定理 `AddGroup.FG.out`：∀ {H : Type u_4} {inst : AddGroup H} [self : AddGroup.F
G H], ⊤.FG
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Group.FG.out`：∀ {G : Type u_3} {inst : Group G} [self : Group.FG G], ⊤.F
G
-/
theorem AddGroup.fg_iff_mul_fg : AddGroup.FG H ↔ Group.FG (Multiplicative H) :=
  ⟨fun h => ⟨(AddSubgroup.fg_iff_mul_fg ⊤).1 h.out⟩, fun h =>
    ⟨(AddSubgroup.fg_iff_mul_fg ⊤).2 h.out⟩⟩
/-
**AddGroup.fg_of_group_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddGroup.fg_of_group_fg [Group.FG G] : AddGroup.FG (Additive G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GroupFG.iff_add_fg`：GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Addit
ive G)
-/
instance AddGroup.fg_of_group_fg [Group.FG G] : AddGroup.FG (Additive G) :=
  GroupFG.iff_add_fg.1 ‹_›
/-
**Group.fg_of_mul_group_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Group.fg_of_mul_group_fg [AddGroup.FG H] : Group.FG (Multiplicative H)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddGroup.fg_iff_mul_fg`：AddGroup.fg_iff_mul_fg : AddGroup.FG H ↔ Group.F
G (Multiplicative H)
-/
instance Group.fg_of_mul_group_fg [AddGroup.FG H] : Group.FG (Multiplicative H) :=
  AddGroup.fg_iff_mul_fg.1 ‹_›

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Group.fg_of_finite [Finite G] : Group.FG G := by
  cases nonempty_fintype G
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Subgroup.closure_univ⟩⟩

@[to_additive]
/-
**Group.fg_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.fg_of_surjective {G' : Type*} [Group G'] [hG : Group.FG G] {f : G ->
* G'} (hf : Function.Surjective f) : Group.FG G'
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Group.fg_iff_monoid_fg`：Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG 
G
· 使用定理 `Monoid.fg_of_surjective`：Monoid.fg_of_surjective {M' : Type*} [Monoid M'
] [Monoid.FG M] (f : M ->* M') (hf : Function.Surjective f) : Monoid.FG M'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Group.fg_of_surjective {G' : Type*} [Group G'] [hG : Group.FG G] {f : G →* G'}
    (hf : Function.Surjective f) : Group.FG G' :=
  Group.fg_iff_monoid_fg.mpr <|
    @Monoid.fg_of_surjective G _ G' _ (Group.fg_iff_monoid_fg.mp hG) f hf

open FreeGroup in
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Finite α] : Group.FG (FreeGroup α) :=
  Group.fg_iff.mpr ⟨Set.range of, closure_range_of α, Set.finite_range of⟩

/-- A group is finitely generated iff there exists a surjective homomorphism from a `FreeGroup`
on finitely many generators. -/
@[to_additive /-- An additive group is finitely generated iff there exists a surjective homomorphism
from a `FreeAddGroup` on finitely many generators. -/]
/-
**Group.fg_iff_exists_freeGroup_hom_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.fg_iff_exists_freeGroup_hom_surjective : Group.FG G ↔ exists (S : Se
t G) (_ : S.Finite) (φ : FreeGroup S ->* G), Function.Surjective φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `FreeGroup.closure_eq_range`：closure_eq_range (s : Set β) : Subgroup.clos
ure s = (lift ((↑) : s -> β)).range
· 使用定理 `Group.fg_of_surjective`：Group.fg_of_surjective {G' : Type*} [Group G'] [
hG : Group.FG G] {f : G ->* G'} (hf : Function.Surjective f) : Group.FG G'
· 使用定理 `instFGFreeGroupOfFinite`：∀ (α : Type u_5) [Finite α], Group.FG (FreeGrou
p α)
-/
theorem Group.fg_iff_exists_freeGroup_hom_surjective :
    Group.FG G ↔ ∃ (S : Set G) (_ : S.Finite) (φ : FreeGroup S →* G), Function.Surjective φ := by
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨S, S.finite_toSet, FreeGroup.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.range_eq_top, ← FreeGroup.closure_eq_range]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    exact Group.fg_of_surjective hφ

/-- A group if finitely generated if and only if there exists a surjective homomorphism from a
`FreeGroup` on an arbitrary finite type `α` to the group. -/
@[to_additive /-- An additive group is finitely generated iff there exists a surjective homomorphism
from a `FreeAddGroup` on an arbitrary finite type `α` to the group. -/]
/-
**Group.fg_iff_exists_freeGroup_hom_surjective_finite** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Group.fg_iff_exists_freeGroup_hom_surjective_finite : Group.FG G ↔ exists 
(α : Type) (_ : Finite α) (φ : FreeGroup α ->* G), Function.Surjective φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.fg_iff_exists_freeGroup_hom_surjective`：Group.fg_iff_exists_freeGr
oup_hom_surjective : Group.FG G ↔ exists (S : Set G) (_ : S.Finite) (φ : FreeGro
up S ->* G), Function.Surjective φ
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `Group.fg_of_surjective`：Group.fg_of_surjective {G' : Type*} [Group G'] [
hG : Group.FG G] {f : G ->* G'} (hf : Function.Surjective f) : Group.FG G'
· 使用定理 `instFGFreeGroupOfFinite`：∀ (α : Type u_5) [Finite α], Group.FG (FreeGrou
p α)
-/
theorem Group.fg_iff_exists_freeGroup_hom_surjective_finite :
    Group.FG G ↔ ∃ (α : Type) (_ : Finite α) (φ : FreeGroup α →* G), Function.Surjective φ := by
  constructor
  · rw [fg_iff_exists_freeGroup_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeGroup.freeGroupCongr e).symm,
      hφ.comp (FreeGroup.freeGroupCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Group.fg_of_surjective hφ

@[to_additive]
/-
**Group.fg_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Group.fg_range {G' : Type*} [Group G'] [Group.FG G] (f : G ->* G') : Group
.FG f.range
参数：f : G ->* G'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.fg_of_surjective`：Group.fg_of_surjective {G' : Type*} [Group G'] [
hG : Group.FG G] {f : G ->* G'} (hf : Function.Surjective f) : Group.FG G'
· 使用定理 `MonoidHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : G ->* 
N) : Function.Surjective f.rangeRestrict
-/
instance Group.fg_range {G' : Type*} [Group G'] [Group.FG G] (f : G →* G') : Group.FG f.range :=
  Group.fg_of_surjective f.rangeRestrict_surjective

@[to_additive]
/-
**Group.closure_finset_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Group.closure_finset_fg (s : Finset G) : Group.FG (Subgroup.closure (s : S
et G))
参数：s : Finset G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.coe_subtype`：coe_subtype : ⇑H.subtype = ((↑) : H -> G)
· 使用定理 `Subgroup.closure_preimage_eq_top`：closure_preimage_eq_top (s : Set G) : 
closure ((closure s).subtype ⁻¹' s) = ⊤
-/
instance Group.closure_finset_fg (s : Finset G) : Group.FG (Subgroup.closure (s : Set G)) := by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage, ← Subgroup.coe_subtype, Subgroup.closure_preimage_eq_top]

@[to_additive]
/-
**Group.closure_finite_fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Group.closure_finite_fg (s : Set G) [Finite s] : Group.FG (Subgroup.closur
e s)
参数：s : Set G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
-/
instance Group.closure_finite_fg (s : Set G) [Finite s] : Group.FG (Subgroup.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Group.closure_finset_fg s.toFinset

end Group

section QuotientGroup

@[to_additive]
/-
**QuotientGroup.fg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：QuotientGroup.fg [Group.FG G] (N : Subgroup G) [Subgroup.Normal N] : Group
.FG G ⧸ N
参数：N : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.fg_of_surjective`：Group.fg_of_surjective {G' : Type*} [Group G'] [
hG : Group.FG G] {f : G ->* G'} (hf : Function.Surjective f) : Group.FG G'
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
-/
instance QuotientGroup.fg [Group.FG G] (N : Subgroup G) [Subgroup.Normal N] : Group.FG <| G ⧸ N :=
  Group.fg_of_surjective <| QuotientGroup.mk'_surjective N

end QuotientGroup

namespace Prod

variable [Monoid N] {G' : Type*} [Group G']

open Monoid in
/-- The product of two finitely generated monoids is finitely generated. -/
@[to_additive /-- The product of two finitely generated additive monoids is finitely generated. -/]
/-
**Prod.instMonoidFG** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instMonoidFG [FG M] [FG N] : FG (M × N) where fg_top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.top_prod_top`：top_prod_top : (⊤ : Submonoid M).prod (⊤ : Submo
noid N) = ⊤
· 使用定理 `Submonoid.FG.prod`：Submonoid.FG.prod (hP : P.FG) (hQ : Q.FG) : (P.prod Q
).FG
· 使用定理 `Monoid.FG.fg_top`：∀ {M : Type u_1} {inst : Monoid M} [self : Monoid.FG M
], ⊤.FG

--- 原说明 ---
The product of two finitely generated monoids is finitely generated.
-/
instance instMonoidFG [FG M] [FG N] : FG (M × N) where
  fg_top := by
    rw [← Submonoid.top_prod_top]
    exact ‹FG M›.fg_top.prod ‹FG N›.fg_top

open Group in
/-- The product of two finitely generated groups is finitely generated. -/
@[to_additive /-- The product of two finitely generated additive groups is finitely generated. -/]
/-
**Prod.instGroupFG** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instGroupFG [FG G] [FG G'] : FG (G × G') where out
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.top_prod_top`：top_prod_top : (⊤ : Subgroup G).prod (⊤ : Subgrou
p N) = ⊤
· 使用定理 `Subgroup.FG.prod`：Subgroup.FG.prod {G' : Type*} [Group G'] {P : Subgroup
 G} {Q : Subgroup G'} (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG
· 使用定理 `Group.FG.out`：∀ {G : Type u_3} {inst : Group G} [self : Group.FG G], ⊤.F
G

--- 原说明 ---
The product of two finitely generated groups is finitely generated.
-/
instance instGroupFG [FG G] [FG G'] : FG (G × G') where
  out := by
    rw [← Subgroup.top_prod_top]
    exact ‹FG G›.out.prod ‹FG G'›.out

end Prod

namespace Pi

variable {ι : Type*} [Finite ι]

/-- Finite product of finitely generated monoids is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive monoids is finitely generated. -/]
/-
**Pi.instMonoidFG** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instMonoidFG {M : ι -> Type*} [forall i, Monoid (M i)] [forall i, Monoid.F
G (M i)] : Monoid.FG (forall i, M i) where fg_top
参数：M i；M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.pi_top`：pi_top (I : Set ι) : (pi I fun i => (⊤ : Submonoid (M 
i))) = ⊤
· 使用定理 `Submonoid.FG.pi`：Submonoid.FG.pi (hP : forall i, (P i).FG) : (pi Set.uni
v P).FG
· 使用定理 `Monoid.FG.fg_top`：∀ {M : Type u_1} {inst : Monoid M} [self : Monoid.FG M
], ⊤.FG

--- 原说明 ---
Finite product of finitely generated monoids is finitely generated.
-/
instance instMonoidFG {M : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid.FG (M i)] :
    Monoid.FG (∀ i, M i) where
  fg_top := by
    rw [← Submonoid.pi_top Set.univ]
    exact .pi fun i => Monoid.FG.fg_top

/-- Finite product of finitely generated groups is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive groups is finitely generated. -/]
/-
**Pi.instGroupFG** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instGroupFG {G : ι -> Type*} [forall i, Group (G i)] [forall i, Group.FG (
G i)] : Group.FG (forall i, G i) where out
参数：G i；G i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.pi_top`：pi_top (I : Set η) : (pi I fun i => (⊤ : Subgroup (f i)
)) = ⊤
· 使用定理 `Subgroup.FG.pi`：Subgroup.FG.pi {ι : Type*} [Finite ι] {G : ι -> Type*} [
forall i, Group (G i)] {P : forall i, Subgroup (G i)} (hP : forall i, (P i).FG) 
: (p…
· 使用定理 `Group.FG.out`：∀ {G : Type u_3} {inst : Group G} [self : Group.FG G], ⊤.F
G

--- 原说明 ---
Finite product of finitely generated groups is finitely generated.
-/
instance instGroupFG {G : ι → Type*} [∀ i, Group (G i)] [∀ i, Group.FG (G i)] :
    Group.FG (∀ i, G i) where
  out := by
    rw [← Subgroup.pi_top Set.univ]
    exact .pi fun i => Group.FG.out

end Pi

namespace AddMonoid

/-
**AddMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FG ℕ where
  fg_top := ⟨{1}, by simp⟩

end AddMonoid

namespace AddGroup

/-
**AddGroup.** 是 Mathlib 中的一个实例，位于命名空间 `AddGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FG ℤ where
  out := ⟨{1}, by simp⟩

end AddGroup

section WellQuasiOrderedLE

variable {M N : Type*} [CommMonoid M] [PartialOrder M] [WellQuasiOrderedLE M]
  [IsOrderedCancelMonoid M] [CanonicallyOrderedMul M]

/-- In a canonically ordered and well-quasi-ordered monoid, any divisive submonoid is finitely
generated. -/
@[to_additive fg_of_subtractive /-- In a canonically ordered and well-quasi-ordered additive monoid
(typical example is `ℕ ^ k`), any subtractive submonoid is finitely generated. -/]
/-
**Submonoid.fg_of_divisive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.fg_of_divisive {P : Submonoid M} (hP : forall x in P, forall y, 
x * y in P -> y in P) : P.FG
参数：hP : forall x in P, forall y, x * y in P -> y in P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.isPWO_of_wellQuasiOrderedLE`：isPWO_of_wellQuasiOrderedLE [h : WellQu
asiOrderedLE α] (s : Set α) : s.IsPWO
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.fg_iff`：Submonoid.fg_iff (P : Submonoid M) : Submonoid.FG P ↔ 
exists S : Set M, Submonoid.closure S = P ∧ S.Finite
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `Submonoid.closure_mono`：closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : 
closure s <= closure t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `setOfPred_minimal_subset`：setOfPred_minimal_subset (s : Set α) : {x | Mi
nimal (· in s) x} subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Set.WellFoundedOn.induction`：∀ {α : Type u_2} {r : α → α → Prop} {s : Se
t α} {x : α},   s.WellFoundedOn r → x ∈ s → ∀ {P : α → Prop}, (∀ y ∈ s, (∀ z ∈ s
, r z y → P z) → …
· 使用定理 `Set.PartiallyWellOrderedOn.wellFoundedOn`：∀ {α : Type u_2} {r : α → α → 
Prop} {s : Set α} [IsPreorder α r],   s.PartiallyWellOrderedOn r → s.WellFounded
On fun a b => r a b ∧ ¬r b a
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `Submonoid.mem_closure_of_mem`：mem_closure_of_mem {s : Set M} {x : M} (hx
 : x in s) : x in closure s
· 使用定理 `exists_lt_of_not_minimal`：∀ {α : Type u_2} {P : α → Prop} {x : α} [inst 
: Preorder α], P x → ¬Minimal P x → ∃ y < x, P y
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
· 使用定理 `CanonicallyOrderedMul.toExistsMulOfLE`：∀ {α : Type u_1} {inst : Mul α} {
inst_1 : LE α} [self : CanonicallyOrderedMul α], ExistsMulOfLE α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `one_lt_of_lt_mul_right`：one_lt_of_lt_mul_right [MulLeftReflectLT α] {a b
 : α} (h : a < a * b) : 1 < b
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `le_mul_self`：le_mul_self : a <= b * a
（共 42 条，此处仅展示前 30 条）
-/
theorem Submonoid.fg_of_divisive {P : Submonoid M} (hP : ∀ x ∈ P, ∀ y, x * y ∈ P → y ∈ P) :
    P.FG := by
  have hpwo := Set.isPWO_of_wellQuasiOrderedLE { x | x ∈ P ∧ x ≠ 1 }
  rw [fg_iff]
  refine ⟨_, ?_, (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOfPred_minimal_subset _))⟩
  ext x
  constructor
  · intro hx
    rw [← P.closure_eq]
    exact closure_mono ((setOfPred_minimal_subset _).trans fun _ => And.left) hx
  · intro hx₁
    by_cases hx₂ : x = 1
    · simp [hx₂]
    refine hpwo.wellFoundedOn.induction ⟨hx₁, hx₂⟩ fun y ⟨hy₁, hy₂⟩ ih => ?_
    simp only [Set.mem_ofPred_eq, and_imp] at ih
    by_cases hy₃ : Minimal (· ∈ { x | x ∈ P ∧ x ≠ 1 }) y
    · exact mem_closure_of_mem hy₃
    rcases exists_lt_of_not_minimal ⟨hy₁, hy₂⟩ hy₃ with ⟨z, hz₁, hz₂, hz₃⟩
    rcases exists_mul_of_le hz₁.le with ⟨y, rfl⟩
    apply mul_mem
    · exact ih _ hz₂ hz₃ hz₁.le hz₁.not_ge
    apply ih
    · exact hP _ hz₂ _ hy₁
    · exact (one_lt_of_lt_mul_right hz₁).ne.symm
    · exact le_mul_self
    · rw [mul_le_iff_le_one_left']
      exact (one_lt_of_ne_one hz₃).not_ge

/-- A canonically ordered and well-quasi-ordered monoid must be finitely generated. -/
@[to_additive /-- A canonically ordered and well-quasi-ordered additive monoid must be finitely
generated. -/]
/-
**CommMonoid.fg_of_wellQuasiOrderedLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommMonoid.fg_of_wellQuasiOrderedLE : Monoid.FG M where fg_top
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.fg_of_divisive`：Submonoid.fg_of_divisive {P : Submonoid M} (hP
 : forall x in P, forall y, x * y in P -> y in P) : P.FG
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem CommMonoid.fg_of_wellQuasiOrderedLE : Monoid.FG M where
  fg_top := Submonoid.fg_of_divisive (by simp)

/-- If `f` `g` are homomorphisms from a canonically ordered and well-quasi-ordered monoid `M` to a
cancellative monoid `N`, the submonoid of `M` on which `f` and `g` agree is finitely generated. -/
@[to_additive /-- If `f` `g` are homomorphisms from a canonically ordered and well-quasi-ordered
additive monoid `M` to a cancellative additive monoid `N`, the submonoid of `M` on which `f` and `g`
agree is finitely generated. When `M` and `N` are `ℕ ^ k`, this is also known as a version of
**Gordan's lemma**. -/]
/-
**Submonoid.fg_eqLocusM** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.fg_eqLocusM [Monoid N] [IsCancelMul N] (f g : M ->* N) : (f.eqLo
cusM g).FG
参数：f g : M ->* N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.fg_of_divisive`：Submonoid.fg_of_divisive {P : Submonoid M} (hP
 : forall x in P, forall y, x * y in P -> y in P) : P.FG
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Submonoid.fg_eqLocusM [Monoid N] [IsCancelMul N] (f g : M →* N) : (f.eqLocusM g).FG :=
  fg_of_divisive (by simp_all)

end WellQuasiOrderedLE

