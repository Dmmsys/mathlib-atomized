/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# Inner fibrations

Inner fibrations of simplicial sets are the morphisms in `SSet` which have the right lifting
property with respect to all inner horn inclusions.

Basic consequences of inner fibrations with respect to the definition of quasi-categories are
formalized.

-/

public section

open CategoryTheory MorphismProperty Simplicial Limits

universe u

namespace SSet

/-- The family of morphisms in `SSet` which consists of inner horn inclusions
`Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]` (for `0 < i < n`). -/
/-
**SSet.innerHornInclusions** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：CategoryTheory.MorphismProperty _root_.SSet
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of morphisms in `SSet` which consists of inner horn inclusions
`Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]` (for `0 < i < n`).
-/
inductive innerHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    innerHornInclusions Λ[n + 2, i].ι
/-
**SSet.horn_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma horn_ι_mem_innerHornInclusions {n : ℕ} {i : Fin (n + 1)}
    (h0 : 0 < i) (hn : i < Fin.last n) : innerHornInclusions (horn.{u} n i).ι := by
  obtain _ | _ | k := n
  · grind
  · grind
  · exact ⟨i, h0, hn⟩
/-
**SSet.innerHornInclusions_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：innerHornInclusions_eq_iSup : innerHornInclusions.{u} = ⨆ n, .ofHoms (fun 
p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} => Λ[n + 2, p].ι)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `SSet.horn_ι_mem_innerHornInclusions`：horn_ι_mem_innerHornInclusions {n :
 Nat} {i : Fin (n + 1)} (h0 : 0 < i) (hn : i < Fin.last n) : innerHornInclusions
 (horn.{u} n i).ι
-/
lemma innerHornInclusions_eq_iSup :
    innerHornInclusions.{u} =
    ⨆ n, .ofHoms (fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} ↦ Λ[n + 2, p].ι) := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain @⟨n, i, h0, hn⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    use n, i
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, h0, hn⟩, _, _⟩ := h
    exact horn_ι_mem_innerHornInclusions h0 hn
/-
**SSet.innerHornInclusions_le_J** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：innerHornInclusions_le_J : innerHornInclusions.{u} <= modelCategoryQuillen
.J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `SSet.modelCategoryQuillen.horn_ι_mem_J`：horn_ι_mem_J (n : Nat) [NeZero n
] (i : Fin (n + 1)) : J (horn.{u} n i).ι
-/
lemma innerHornInclusions_le_J : innerHornInclusions.{u} ≤ modelCategoryQuillen.J :=
  fun _ _ _ ⟨_, _, _⟩ ↦ modelCategoryQuillen.horn_ι_mem_J ..
/-
**SSet.innerHornInclusions_le_monomorphisms** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：innerHornInclusions_le_monomorphisms : innerHornInclusions.{u} <= monomorp
hisms SSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SSet.innerHornInclusions_le_J`：innerHornInclusions_le_J : innerHornInclu
sions.{u} <= modelCategoryQuillen.J
· 使用引理 `SSet.modelCategoryQuillen.J_le_monomorphisms`：J_le_monomorphisms : J.{u}
 <= monomorphisms _
-/
lemma innerHornInclusions_le_monomorphisms :
    innerHornInclusions.{u} ≤ monomorphisms SSet :=
  innerHornInclusions_le_J.trans modelCategoryQuillen.J_le_monomorphisms

/-- The inner fibrations are the morphisms which have the right lifting property
with respect to inner horn inclusions. -/
@[expose, kerodon 01BA]
/-
**SSet.innerFibrations** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：innerFibrations : MorphismProperty SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inner fibrations are the morphisms which have the right lifting property
with respect to inner horn inclusions.
-/
def innerFibrations : MorphismProperty SSet.{u} := innerHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

/-- A morphism `q` satisfies `[InnerFibration q]` if it belongs to `innerFibrations`. -/
@[mk_iff]
/-
**SSet.InnerFibration** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：{X Y : _root_.SSet} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `q` satisfies `[InnerFibration q]` if it belongs to `innerFibrations`
.
-/
class InnerFibration {X Y : SSet} (q : X ⟶ Y) : Prop where
  mem : innerFibrations q
/-
**SSet.mem_innerFibrations** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：mem_innerFibrations {X Y : SSet} (q : X ⟶ Y) [InnerFibration q] : innerFib
rations q
参数：q : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.InnerFibration.mem`：∀ {X Y : _root_.SSet} {q : X ⟶ Y} [self : SSet.
InnerFibration q], SSet.innerFibrations q
-/
lemma mem_innerFibrations {X Y : SSet} (q : X ⟶ Y) [InnerFibration q] : innerFibrations q :=
  InnerFibration.mem
/-
**SSet.quasicategory_iff_innerFibration** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：quasicategory_iff_innerFibration (X : SSet.{u}) : Quasicategory X ↔ InnerF
ibration (terminal.from X)
参数：X : SSet.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.quasicategory_iff_hasLiftingProperty`：quasicategory_iff_hasLiftingP
roperty (S : SSet) {X : SSet} (t : Limits.IsTerminal X) : Quasicategory S ↔ fora
ll {n : Nat} {i : Fin (n + 1)} …
· 使用定理 `SSet.innerFibration_iff`：∀ {X Y : _root_.SSet} (q : X ⟶ Y), SSet.InnerFi
bration q ↔ SSet.innerFibrations q
· 使用引理 `SSet.horn_ι_mem_innerHornInclusions`：horn_ι_mem_innerHornInclusions {n :
 Nat} {i : Fin (n + 1)} (h0 : 0 < i) (hn : i < Fin.last n) : innerHornInclusions
 (horn.{u} n i).ι
-/
lemma quasicategory_iff_innerFibration (X : SSet.{u}) :
    Quasicategory X ↔ InnerFibration (terminal.from X) := by
  rw [quasicategory_iff_hasLiftingProperty.{u} _ terminalIsTerminal, innerFibration_iff]
  exact ⟨fun h _ _ _ ⟨i, h0, hn⟩ ↦ h h0 hn,
    fun h _ _ h0 hn ↦ h _ (horn_ι_mem_innerHornInclusions h0 hn)⟩

@[kerodon 01BB]
/-
**SSet.quasicategory_iff_of_isTerminal** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：quasicategory_iff_of_isTerminal {X Y : SSet} (p : X ⟶ Y) (hY : IsTerminal 
Y) : Quasicategory X ↔ InnerFibration p
参数：p : X ⟶ Y；hY : IsTerminal Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `SSet.instRespectsIsoInnerFibrations`：SSet.innerFibrations.RespectsIso
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `CategoryTheory.Limits.IsTerminal.uniqueUpToIso_hom`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {T T' : C} (hT : CategoryTheory.Limits.I
sTerminal T)   (hT' : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
-/
lemma quasicategory_iff_of_isTerminal
    {X Y : SSet} (p : X ⟶ Y) (hY : IsTerminal Y) :
    Quasicategory X ↔ InnerFibration p := by
  simp only [quasicategory_iff_innerFibration, innerFibration_iff]
  symm
  apply innerFibrations.arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (Limits.IsTerminal.uniqueUpToIso hY Limits.terminalIsTerminal)

@[kerodon 01BJ]
/-
**SSet.quasicategory_of_innerFibration** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：quasicategory_of_innerFibration {X Y : SSet} (p : X ⟶ Y) [InnerFibration p
] [hY : Quasicategory Y] : Quasicategory X
参数：p : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.quasicategory_iff_innerFibration`：quasicategory_iff_innerFibration 
(X : SSet.{u}) : Quasicategory X ↔ InnerFibration (terminal.from X)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `SSet.innerFibration_iff`：∀ {X Y : _root_.SSet} (q : X ⟶ Y), SSet.InnerFi
bration q ↔ SSet.innerFibrations q
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `SSet.instIsMultiplicativeInnerFibrations`：SSet.innerFibrations.IsMultipl
icative
· 使用定理 `SSet.InnerFibration.mem`：∀ {X Y : _root_.SSet} {q : X ⟶ Y} [self : SSet.
InnerFibration q], SSet.innerFibrations q
-/
lemma quasicategory_of_innerFibration
    {X Y : SSet} (p : X ⟶ Y) [InnerFibration p] [hY : Quasicategory Y] :
    Quasicategory X := by
  rw [quasicategory_iff_innerFibration] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y), innerFibration_iff]
  refine innerFibrations.comp_mem _ _ InnerFibration.mem hY.mem
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : SSet} [Quasicategory X] : InnerFibration (terminal.from X) := by
  rwa [← quasicategory_iff_innerFibration]

@[deprecated quasicategory_iff_of_isTerminal (since := "2026-06-08")]
/-
**SSet.quasicategory_of_from_innerFibrations** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：quasicategory_of_from_innerFibrations (S : SSet) {X : SSet} (t : Limits.Is
Terminal X) (h : innerFibrations (t.from S)) : Quasicategory S
参数：S : SSet；t : Limits.IsTerminal X；h : innerFibrations (t.from S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.quasicategory_of_hasLiftingProperty`：quasicategory_of_hasLiftingPro
perty (S : SSet) {X : SSet} (t : Limits.IsTerminal X) (h : forall {n : Nat} {i :
 Fin (n + 1)} (_ : 0 < i) (_ :…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `SSet.horn_ι_mem_innerHornInclusions`：horn_ι_mem_innerHornInclusions {n :
 Nat} {i : Fin (n + 1)} (h0 : 0 < i) (hn : i < Fin.last n) : innerHornInclusions
 (horn.{u} n i).ι
-/
lemma quasicategory_of_from_innerFibrations (S : SSet) {X : SSet} (t : Limits.IsTerminal X)
    (h : innerFibrations (t.from S)) : Quasicategory S :=
  quasicategory_of_hasLiftingProperty S t (fun h0 hn ↦ h _ (horn_ι_mem_innerHornInclusions h0 hn))

@[deprecated quasicategory_iff_of_isTerminal (since := "2026-06-08")]
/-
**SSet.Quasicategory.from_innerFibrations** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Quasic
ategory`。
形式化陈述：∀ (S : _root_.SSet) [S.Quasicategory] {X : _root_.SSet} (t : CategoryTheor
y.Limits.IsTerminal X),   SSet.innerFibrations (t.from S)
参数：S : _root_.SSet；t : CategoryTheory.Limits.IsTerminal X；t.from S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SSet.Quasicategory.hasLiftingProperty`：∀ (S : _root_.SSet) [S.Quasicateg
ory] {X : _root_.SSet} (t : CategoryTheory.Limits.IsTerminal X) {n : ℕ}   {i : F
in (n + 1)}, 0 < i → i < Fi…
-/
lemma Quasicategory.from_innerFibrations (S : SSet) [Quasicategory S]
    {X : SSet} (t : Limits.IsTerminal X) : innerFibrations (t.from S) :=
  fun _ _ _ ⟨_, h0, hn⟩ ↦ hasLiftingProperty S t h0 hn

@[deprecated (since := "2026-06-08")]
alias quasicategory_iff_from_innerFibration := quasicategory_iff_innerFibration

@[deprecated (since := "2026-06-08")]
alias quasicategory_of_innerFibration_quasicategory := quasicategory_of_innerFibration

end SSet

