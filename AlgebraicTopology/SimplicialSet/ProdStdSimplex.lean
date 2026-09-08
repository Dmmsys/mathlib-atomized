/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.Order.Preorder.Finite

/-!
# Binary product of standard simplices

In this file, we show that `Δ[p] ⊗ Δ[q]` identifies to the nerve of
`ULift (Fin (p + 1) × Fin (q + 1))`. We relate the `n`-simplices
of `Δ[p] ⊗ Δ[q]` to order preserving maps `Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`,
Via this bijection, a simplex in `Δ[p] ⊗ Δ[q]` is nondegenerate iff
the corresponding monotone map `Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`
is injective (or a strict mono).

We also show that the dimension of `Δ[p] ⊗ Δ[q]` is `≤ p + q`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory

namespace SSet

namespace prodStdSimplex

variable {p q : ℕ}

/-- `n`-simplices in `Δ[p] ⊗ Δ[q]` identify to order preserving maps
`Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`. -/
/-
**SSet.prodStdSimplex.objEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodStdSimplex`。
形式化陈述：objEquiv {n : Nat} : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌ ≃ (Fin (n + 1) ->o
 Fin (p + 1) × Fin (q + 1)) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`n`-simplices in `Δ[p] ⊗ Δ[q]` identify to order preserving maps
`Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`.
-/
def objEquiv {n : ℕ} :
    (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌ ≃ (Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) where
  toFun := fun ⟨x, y⟩ ↦ OrderHom.prod
      (stdSimplex.objEquiv x).toOrderHom
      (stdSimplex.objEquiv y).toOrderHom
  invFun f :=
    ⟨stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.fst.comp f)),
      stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.snd.comp f))⟩
  left_inv := fun ⟨x, y⟩ ↦ by simp

@[simp]
/-
**SSet.prodStdSimplex.objEquiv_apply_fst** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStd
Simplex`。
形式化陈述：objEquiv_apply_fst {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (i :
 Fin (n + 1)) : dsimp% (objEquiv x i).1 = x.1 i
参数：x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objEquiv_apply_fst {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1)) :
    dsimp% (objEquiv x i).1 = x.1 i := rfl

@[simp]
/-
**SSet.prodStdSimplex.objEquiv_apply_snd** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStd
Simplex`。
形式化陈述：objEquiv_apply_snd {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (i :
 Fin (n + 1)) : dsimp% (objEquiv x i).2 = x.2 i
参数：x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objEquiv_apply_snd {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1)) :
    dsimp% (objEquiv x i).2 = x.2 i := rfl
/-
**SSet.prodStdSimplex.objEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodSt
dSimplex`。
形式化陈述：objEquiv_naturality {m n : Nat} (f : ⦋m⦌ ⟶ ⦋n⦌) (z : (Δ[p] otimes Δ[q] : S
Set.{u}) _⦋n⦌) : (objEquiv z).comp f.toOrderHom = objEquiv ((Δ[p] otimes Δ[q]).m
ap f.op z)
参数：f : ⦋m⦌ ⟶ ⦋n⦌；z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objEquiv_naturality {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) :
    (objEquiv z).comp f.toOrderHom = objEquiv ((Δ[p] ⊗ Δ[q]).map f.op z) :=
  rfl
/-
**SSet.prodStdSimplex.objEquiv_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStd
Simplex`。
形式化陈述：objEquiv_map_apply {n m : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (f
 : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) : objEquiv ((Δ[p] otimes Δ[q]).map f.op x) i = o
bjEquiv x (f.toOrderHom i)
参数：x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌；f : ⦋m⦌ ⟶ ⦋n⦌；i : Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objEquiv_map_apply {n m : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
      objEquiv ((Δ[p] ⊗ Δ[q]).map f.op x) i = objEquiv x (f.toOrderHom i) :=
  rfl
/-
**SSet.prodStdSimplex.objEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objEquiv_δ_apply {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n + 1⦌) (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    objEquiv ((Δ[p] ⊗ Δ[q]).δ i x) j = objEquiv x (i.succAbove j) := rfl

variable (p q) in
/-- The binary product `Δ[p] ⊗ Δ[q]` identifies to the nerve
of `ULift (Fin (p + 1) × Fin (q + 1))`. -/
/-
**SSet.prodStdSimplex.isoNerve** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodStdSimplex`。
形式化陈述：isoNerve : Δ[p] otimes Δ[q] ≅ nerve (ULift.{u} (Fin (p + 1) × Fin (q + 1))
)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The binary product `Δ[p] ⊗ Δ[q]` identifies to the nerve
of `ULift (Fin (p + 1) × Fin (q + 1))`.
-/
def isoNerve : Δ[p] ⊗ Δ[q] ≅ nerve (ULift.{u} (Fin (p + 1) × Fin (q + 1))) :=
  NatIso.ofComponents (fun ⟨⟨d⟩⟩ ↦ Equiv.toIso (objEquiv.trans
      { toFun f := (ULift.orderIso.symm.monotone.comp f.monotone).functor
        invFun s := ULift.orderIso.toOrderEmbedding.toOrderHom.comp ⟨_, s.monotone⟩ }))
/-
**SSet.prodStdSimplex.nonDegenerate_iff_injective_objEquiv** 是 Mathlib 中的一个引理，位于
命名空间 `SSet.prodStdSimplex`。
形式化陈述：nonDegenerate_iff_injective_objEquiv {n : Nat} (z : (Δ[p] otimes Δ[q] : SS
et.{u}) _⦋n⦌) : z in (Δ[p] otimes Δ[q]).nonDegenerate n ↔ Function.Injective (ob
jEquiv z)
参数：z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.nonDegenerate_iff_of_mono`：nonDegenerate_iff_of_mono {Y : SSet.{u}}
 (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) : f.app _ x in Y.nonDegenerate n ↔ x in X.non
Degenerate n
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `PartialOrder.mem_nerve_nonDegenerate_iff_injective`：mem_nerve_nonDegener
ate_iff_injective (s : (nerve X) _⦋n⦌) : s in (nerve X).nonDegenerate n ↔ Functi
on.Injective s.obj
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `ULift.down_injective`：∀ {α : Type u_1}, Function.Injective ULift.down
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonDegenerate_iff_injective_objEquiv {n : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) :
    z ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate n ↔ Function.Injective (objEquiv z) := by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom,
    PartialOrder.mem_nerve_nonDegenerate_iff_injective,
    ← Function.Injective.of_comp_iff ULift.down_injective]
  rfl
/-
**SSet.prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv** 是 Mathlib 中的一个引理，位
于命名空间 `SSet.prodStdSimplex`。
形式化陈述：nonDegenerate_iff_strictMono_objEquiv {n : Nat} (z : (Δ[p] otimes Δ[q] : S
Set.{u}) _⦋n⦌) : z in (Δ[p] otimes Δ[q]).nonDegenerate n ↔ StrictMono (objEquiv 
z)
参数：z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.nonDegenerate_iff_of_mono`：nonDegenerate_iff_of_mono {Y : SSet.{u}}
 (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) : f.app _ x in Y.nonDegenerate n ↔ x in X.non
Degenerate n
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `PartialOrder.mem_nerve_nonDegenerate_iff_strictMono`：mem_nerve_nonDegene
rate_iff_strictMono (s : (nerve X) _⦋n⦌) : s in (nerve X).nonDegenerate n ↔ Stri
ctMono s.obj
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonDegenerate_iff_strictMono_objEquiv {n : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) :
    z ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate n ↔ StrictMono (objEquiv z) := by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom,
    PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl

/-- Given a `n`-simplex `x` in `Δ[p] ⊗ Δ[q]`, this is the order preserving
map `Fin (n + 1) →o Fin (m + 1)` (with `p + q = m`) which corresponds to the
sum of the two components of `objEquiv x : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`. -/
@[simps coe]
/-
**SSet.prodStdSimplex.orderHomOfSimplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet.prodStdS
implex`。
形式化陈述：orderHomOfSimplex {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) {m : 
Nat} (hm : p + q = m) : Fin (n + 1) ->o Fin (m + 1) where toFun i
参数：x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌；hm : p + q = m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `n`-simplex `x` in `Δ[p] ⊗ Δ[q]`, this is the order preserving
map `Fin (n + 1) →o Fin (m + 1)` (with `p + q = m`) which corresponds to the
sum of the two components of `objEquiv x : Fin (n + 1) →o Fin (p + 1) × Fin (q +
 1)`.
-/
def orderHomOfSimplex {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) {m : ℕ} (hm : p + q = m) :
    Fin (n + 1) →o Fin (m + 1) where
  toFun i := ⟨(x.1 i : ℕ) + x.2 i, by lia⟩
  monotone' i j h := by
    dsimp
    simp only [Fin.mk_le_mk]
    have := (objEquiv x).monotone h
    have h₁ : x.1 i ≤ x.1 j := this.1
    have h₂ : x.2 i ≤ x.2 j := this.2
    lia
/-
**SSet.prodStdSimplex.strictMono_orderHomOfSimplex_iff** 是 Mathlib 中的一个引理，位于命名空间
 `SSet.prodStdSimplex`。
形式化陈述：strictMono_orderHomOfSimplex_iff {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{
u}) _⦋n⦌) {m : Nat} (hm : p + q = m) : StrictMono (orderHomOfSimplex x hm) ↔ Str
ictMono (objEquiv x)
参数：x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌；hm : p + q = m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.lt_iff`：lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 
< y.2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ
-/
lemma strictMono_orderHomOfSimplex_iff {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) {m : ℕ}
    (hm : p + q = m) :
    StrictMono (orderHomOfSimplex x hm) ↔ StrictMono (objEquiv x) := by
  have (a b : Fin (p + 1) × Fin (q + 1)) (hab : a ≤ b) :
      a < b ↔ ((a.1 : ℕ) + a.2 < (b.1 : ℕ) + b.2) := by
    obtain ⟨h₁, h₂⟩ := hab
    rw [Prod.lt_iff]
    lia
  simp only [Fin.strictMono_iff_lt_succ]
  exact forall_congr' (fun i ↦ (this _ _ ((objEquiv x).monotone i.castSucc_le_succ)).symm)
/-
**SSet.prodStdSimplex.strictMono_orderHomOfSimplex** 是 Mathlib 中的一个引理，位于命名空间 `SS
et.prodStdSimplex`。
形式化陈述：strictMono_orderHomOfSimplex {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}).
nonDegenerate n) {m : Nat} (hm : p + q = m) : StrictMono (orderHomOfSimplex x.1 
hm)
参数：x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n；hm : p + q = m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma strictMono_orderHomOfSimplex {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n) {m : ℕ}
    (hm : p + q = m) :
    StrictMono (orderHomOfSimplex x.1 hm) := by
  simpa only [strictMono_orderHomOfSimplex_iff, ← nonDegenerate_iff_strictMono_objEquiv] using x.2
/-
**SSet.prodStdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Δ[p] ⊗ Δ[q] : SSet.{u}).HasDimensionLE (p + q) where
  degenerate_eq_top n hn := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    by_contra hx
    rw [← mem_nonDegenerate_iff_notMem_degenerate,
      nonDegenerate_iff_strictMono_objEquiv,
      ← strictMono_orderHomOfSimplex_iff _ rfl] at hx
    replace hx := Fintype.card_le_of_injective _ hx.injective
    simp only [Fintype.card_fin, add_le_add_iff_right] at hx
    lia
/-
**SSet.prodStdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Δ[p] ⊗ Δ[q] : SSet.{u}).Finite :=
  finite_of_hasDimensionLT _ (p + q + 1) inferInstance
/-
**SSet.prodStdSimplex.le_orderHomOfSimplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodS
tdSimplex`。
形式化陈述：le_orderHomOfSimplex {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegen
erate n) {m : Nat} (hm : p + q = m) (i : Fin (n + 1)) : i.1 <= orderHomOfSimplex
 x.1 hm i
参数：x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n；hm : p + q = m；i : Fin (n +
 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.prodStdSimplex.orderHomOfSimplex_coe`：∀ {p q n : ℕ}   (x :     (Cat
egoryTheory.MonoidalCategoryStruct.tensorObj (SSet.stdSimplex.obj { len := p }) 
          (SSet.stdSimplex.obj …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `SSet.prodStdSimplex.strictMono_orderHomOfSimplex`：strictMono_orderHomOfS
implex {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n) {m : Nat} (
hm : p + q = m) : StrictMono (orderHom…
· 使用定理 `Fin.castSucc_lt_succ`：∀ {n : ℕ} {i : Fin n}, i.castSucc < i.succ
-/
lemma le_orderHomOfSimplex {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n) {m : ℕ}
    (hm : p + q = m) (i : Fin (n + 1)) : i.1 ≤ orderHomOfSimplex x.1 hm i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    simpa using! lt_of_le_of_lt hi (strictMono_orderHomOfSimplex x hm Fin.castSucc_lt_succ)
/-
**SSet.prodStdSimplex.nonDegenerate_max_dim_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.
prodStdSimplex`。
形式化陈述：nonDegenerate_max_dim_iff {n : Nat} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n
⦌) (hn : p + q = n
参数：z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrderHom.eq_id_of_injective`：OrderHom.eq_id_of_injective {α : Type*} [Li
nearOrder α] [Finite α] (f : α ->o α) (hf : Function.Injective f) : f = .id
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `SSet.prodStdSimplex.strictMono_orderHomOfSimplex`：strictMono_orderHomOfS
implex {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n) {m : Nat} (
hm : p + q = m) : StrictMono (orderHom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.prodStdSimplex.nonDegenerate_iff_injective_objEquiv`：nonDegenerate_
iff_injective_objEquiv {n : Nat} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) : z in
 (Δ[p] otimes Δ[q]).nonDegenerate n ↔ Function…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SSet.prodStdSimplex.orderHomOfSimplex_coe`：∀ {p q n : ℕ}   (x :     (Cat
egoryTheory.MonoidalCategoryStruct.tensorObj (SSet.stdSimplex.obj { len := p }) 
          (SSet.stdSimplex.obj …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nonDegenerate_max_dim_iff {n : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌)
    (hn : p + q = n := by lia) :
    z ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate n ↔ orderHomOfSimplex z hn = .id := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · exact OrderHom.eq_id_of_injective _ (strictMono_orderHomOfSimplex ⟨z, h⟩ hn).injective
  · rw [nonDegenerate_iff_injective_objEquiv]
    intro h a b hab
    simp only [DFunLike.ext_iff, orderHomOfSimplex_coe, OrderHom.id_coe, id_eq] at h
    rw [← h a, ← h b, Fin.ext_iff]
    change ((objEquiv z a).1 : ℕ) + (objEquiv z a).2 = (objEquiv z b).1 + (objEquiv z b).2
    simp only [hab]
/-
**SSet.prodStdSimplex.nonDegenerate_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStdS
implex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonDegenerate_ext₁ {n : ℕ} {z₁ z₂ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n}
    (h : z₁.1.1 = z₂.1.1) (hn : p + q = n := by lia) :
    z₁ = z₂ := by
  ext
  apply objEquiv.injective
  ext i : 3
  · exact DFunLike.congr_fun h i
  · have h₁ := z₁.2
    have h₂ := z₂.2
    rw [nonDegenerate_max_dim_iff] at h₁ h₂
    simpa only [orderHomOfSimplex_coe, h, Fin.ext_iff, add_right_inj]
      using! DFunLike.congr_fun (h₁.trans h₂.symm) i
/-
**SSet.prodStdSimplex.nonDegenerate_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.prodStdS
implex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonDegenerate_ext₂ {n : ℕ} {z₁ z₂ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n}
    (h : z₁.1.2 = z₂.1.2) (hn : p + q = n := by lia) :
    z₁ = z₂ :=
  (nonDegenerateEquivOfIso (β_ _ _)).injective (nonDegenerate_ext₁ h)

end prodStdSimplex

end SSet

