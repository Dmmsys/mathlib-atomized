/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.Artinian.Module

/-!
# Modules of finite length

We define modules of finite length (`IsFiniteLength`) to be finite iterated extensions of
simple modules, and show that a module is of finite length iff it is both Noetherian and Artinian,
iff it admits a composition series.

We do not make `IsFiniteLength` a class, instead we use `[IsNoetherian R M] [IsArtinian R M]`.

## Tags

Finite length, Composition series
-/

public section

variable (R : Type*) [Ring R]

/-- A module of finite length is either trivial or a simple extension of a module known
to be of finite length. -/
/-
**IsFiniteLength** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [inst : Ring R] → (M : Type u_2) → [inst_1 : AddCommGroup
 M] → [_root_.Module R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module of finite length is either trivial or a simple extension of a module kn
own
to be of finite length.
-/
inductive IsFiniteLength : ∀ (M : Type*) [AddCommGroup M] [Module R M], Prop
  | of_subsingleton {M} [AddCommGroup M] [Module R M] [Subsingleton M] : IsFiniteLength M
  | of_simple_quotient {M} [AddCommGroup M] [Module R M] {N : Submodule R M}
      [IsSimpleModule R (M ⧸ N)] : IsFiniteLength N → IsFiniteLength M

attribute [nontriviality] IsFiniteLength.of_subsingleton

variable {R} {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
/-
**LinearEquiv.isFiniteLength** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isFiniteLength (e : M ≃ₗ[R] N) (h : IsFiniteLength R M) : IsFi
niteLength R N
参数：e : M ≃ₗ[R] N；h : IsFiniteLength R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem LinearEquiv.isFiniteLength (e : M ≃ₗ[R] N)
    (h : IsFiniteLength R M) : IsFiniteLength R N := by
  induction h generalizing N with
  | of_subsingleton =>
    have := e.symm.toEquiv.subsingleton; exact .of_subsingleton
  | @of_simple_quotient M _ _ S _ _ ih =>
    have : IsSimpleModule R (N ⧸ Submodule.map (e : M →ₗ[R] N) S) :=
      IsSimpleModule.congr (Submodule.Quotient.equiv S _ e rfl).symm
    exact .of_simple_quotient (ih <| e.submoduleMap S)

variable (R M) in
/-
**exists_compositionSeries_of_isNoetherian_isArtinian** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：exists_compositionSeries_of_isNoetherian_isArtinian [IsNoetherian R M] [Is
Artinian R M] : exists s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.las
t = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `exists_covBy_seq_of_wellFoundedLT_wellFoundedGT`：exists_covBy_seq_of_wel
lFoundedLT_wellFoundedGT (α) [Preorder α] [Nonempty α] [wfl : WellFoundedLT α] [
wfg : WellFoundedGT α] : exists a : N…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `IsMax.eq_top`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderTop 
α] {a : α}, IsMax a → a = ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem exists_compositionSeries_of_isNoetherian_isArtinian [IsNoetherian R M] [IsArtinian R M] :
    ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Submodule R M)
  exact ⟨⟨n, fun i ↦ f i, fun i ↦ hn.2 i i.2⟩, f0.eq_bot, hn.1.eq_top⟩
/-
**isFiniteLength_of_exists_compositionSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isFiniteLength_of_exists_compositionSeries (h : exists s : CompositionSeri
es (Submodule R M), s.head = ⊥ ∧ s.last = ⊤) : IsFiniteLength R M
参数：h : exists s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `LinearEquiv.isFiniteLength`：LinearEquiv.isFiniteLength (e : M ≃ₗ[R] N) (
h : IsFiniteLength R M) : IsFiniteLength R N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `covBy_iff_quot_is_simple`：covBy_iff_quot_is_simple {A B : Submodule R M}
 (hAB : A <= B) : A ⋖ B ↔ IsSimpleModule R (B ⧸ Submodule.comap B.subtype A)
· 使用定理 `CovBy.le`：CovBy.le (h : a ⋖ b) : a <= b
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
-/
theorem isFiniteLength_of_exists_compositionSeries
    (h : ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤) :
    IsFiniteLength R M :=
  Submodule.topEquiv.isFiniteLength <| by
    obtain ⟨s, s_head, s_last⟩ := h
    rw [← s_last]
    suffices ∀ i, IsFiniteLength R (s i) from this (Fin.last _)
    intro i
    induction i using Fin.induction with
    | zero => change IsFiniteLength R s.head; rw [s_head]; exact .of_subsingleton
    | succ i ih =>
      let cov := s.step i
      have := (covBy_iff_quot_is_simple cov.le).mp cov
      have := ((s i.castSucc).comap (s i.succ).subtype).equivMapOfInjective
        _ (Submodule.injective_subtype _)
      rw [Submodule.map_comap_subtype, inf_of_le_right cov.le] at this
      exact .of_simple_quotient (this.symm.isFiniteLength ih)
/-
**isFiniteLength_iff_isNoetherian_isArtinian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isFiniteLength_iff_isNoetherian_isArtinian : IsFiniteLength R M ↔ IsNoethe
rian R M ∧ IsArtinian R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isNoetherian_iff_submodule_quotient`：isNoetherian_iff_submodule_quotient
 (S : Submodule R N) : IsNoetherian R N ↔ IsNoetherian R S ∧ IsNoetherian R (N ⧸
 S)
· 使用定理 `isNoetherian_iff'`：isNoetherian_iff' : IsNoetherian R M ↔ WellFoundedGT 
(Submodule R M)
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `isArtinian_iff_submodule_quotient`：isArtinian_iff_submodule_quotient (S 
: Submodule R P) : IsArtinian R P ↔ IsArtinian R S ∧ IsArtinian R (P ⧸ S)
· 使用定理 `IsSimpleModule.toIsSimpleOrder`：∀ {R : Type u_2} {inst : Ring R} {M : Ty
pe u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : IsSimpl
eModule R M], IsSimp…
· 使用定理 `isFiniteLength_of_exists_compositionSeries`：isFiniteLength_of_exists_com
positionSeries (h : exists s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s
.last = ⊤) : IsFiniteLength R M
· 使用定理 `exists_compositionSeries_of_isNoetherian_isArtinian`：exists_compositionS
eries_of_isNoetherian_isArtinian [IsNoetherian R M] [IsArtinian R M] : exists s 
: CompositionSeries (Submodule R M), s.he…
-/
theorem isFiniteLength_iff_isNoetherian_isArtinian :
    IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M :=
  open scoped IsSimpleOrder in
  ⟨fun h ↦ h.rec (fun {M} _ _ _ ↦ ⟨inferInstance, inferInstance⟩) fun M _ _ {N} _ _ ⟨_, _⟩ ↦
    ⟨(isNoetherian_iff_submodule_quotient N).mpr ⟨‹_›, isNoetherian_iff'.mpr inferInstance⟩,
      (isArtinian_iff_submodule_quotient N).mpr ⟨‹_›, inferInstance⟩⟩,
    fun ⟨_, _⟩ ↦ isFiniteLength_of_exists_compositionSeries
      (exists_compositionSeries_of_isNoetherian_isArtinian R M)⟩
/-
**isFiniteLength_iff_exists_compositionSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isFiniteLength_iff_exists_compositionSeries : IsFiniteLength R M ↔ exists 
s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
· 使用定理 `exists_compositionSeries_of_isNoetherian_isArtinian`：exists_compositionS
eries_of_isNoetherian_isArtinian [IsNoetherian R M] [IsArtinian R M] : exists s 
: CompositionSeries (Submodule R M), s.he…
· 使用定理 `isFiniteLength_of_exists_compositionSeries`：isFiniteLength_of_exists_com
positionSeries (h : exists s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s
.last = ⊤) : IsFiniteLength R M
-/
theorem isFiniteLength_iff_exists_compositionSeries :
    IsFiniteLength R M ↔ ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ :=
  ⟨fun h ↦ have ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
    exists_compositionSeries_of_isNoetherian_isArtinian R M,
    isFiniteLength_of_exists_compositionSeries⟩

open scoped IsSimpleOrder in
/-
**IsSemisimpleModule.finite_tfae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemisimpleModule.finite_tfae [IsSemisimpleModule R M] : List.TFAE [Modul
e.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M, exists s : S
et (Submodule R M), s.Finite ∧ sSupIndep s ∧ sSup s = ⊤ ∧ forall m in s, IsSimpl
eModule R m]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
· 使用定理 `IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top`：exists_sSupInde
p_sSup_simples_eq_top : exists s : Set (Submodule R M), sSupIndep s ∧ sSup s = ⊤
 ∧ forall m in s, IsSimpleModule R m
· 使用定理 `IsSemisimpleModule.instIsNoetherianOfFinite`：∀ {R : Type u_2} [inst : Ri
ng R] {M : Type u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [I
sSemisimpleModule R M] [Module.Fi…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `WellFoundedGT.finite_of_sSupIndep`：WellFoundedGT.finite_of_sSupIndep [We
llFoundedGT α] {s : Set α} (hs : sSupIndep s) : s.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `WellFoundedLT.finite_of_sSupIndep`：WellFoundedLT.finite_of_sSupIndep [We
llFoundedLT α] {s : Set α} (hs : sSupIndep s) : s.Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isNoetherian_top_iff`：isNoetherian_top_iff : IsNoetherian R (⊤ : Submodu
le R M) ↔ IsNoetherian R M
· 使用定理 `LinearEquiv.isArtinian_iff`：LinearEquiv.isArtinian_iff (f : M ≃ₗ[R] P) :
 IsArtinian R M ↔ IsArtinian R P
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `SetCoe.forall'`：SetCoe.forall' {s : Set α} {p : forall x, x in s -> Prop
} : (forall (x) (h : x in s), p x h) ↔ forall x : s, p x.1 x.2
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsSimpleModule.toIsSimpleOrder`：∀ {R : Type u_2} {inst : Ring R} {M : Ty
pe u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : IsSimpl
eModule R M], IsSimp…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsSemisimpleModule.finite_tfae [IsSemisimpleModule R M] :
    List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M,
      ∃ s : Set (Submodule R M), s.Finite ∧ sSupIndep s ∧
        sSup s = ⊤ ∧ ∀ m ∈ s, IsSimpleModule R m] := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  obtain ⟨s, hs⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top R M
  tfae_have 1 ↔ 2 := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩
  tfae_have 2 → 5 := fun _ ↦ ⟨s, WellFoundedGT.finite_of_sSupIndep hs.1, hs⟩
  tfae_have 3 → 5 := fun _ ↦ ⟨s, WellFoundedLT.finite_of_sSupIndep hs.1, hs⟩
  tfae_have 5 → 4 := fun ⟨s, fin, _, sSup_eq_top, simple⟩ ↦ by
    rw [← isNoetherian_top_iff, ← Submodule.topEquiv.isArtinian_iff,
      ← sSup_eq_top, sSup_eq_iSup, ← iSup_subtype'']
    rw [SetCoe.forall'] at simple
    have := fin.to_subtype
    exact ⟨isNoetherian_iSup, isArtinian_iSup⟩
  tfae_have 4 → 2 := And.left
  tfae_have 4 → 3 := And.right
  tfae_finish
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSemisimpleModule R M] [Module.Finite R M] : IsArtinian R M :=
  (IsSemisimpleModule.finite_tfae.out 0 2).mp ‹_›

variable {f : M →ₗ[R] N}
/-
**IsFiniteLength.of_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsFiniteLength.of_injective (H : IsFiniteLength R N) (hf : Function.Inject
ive f) : IsFiniteLength R M
参数：H : IsFiniteLength R N；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
· 使用定理 `isNoetherian_of_injective`：isNoetherian_of_injective [IsNoetherian S P] 
{σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : 
M ->ₛₗ[σ] P) (h…
· 使用定理 `isArtinian_of_injective`：isArtinian_of_injective (f : M ->ₗ[R] P) (h : F
unction.Injective f) [IsArtinian R P] : IsArtinian R M
-/
lemma IsFiniteLength.of_injective (H : IsFiniteLength R N) (hf : Function.Injective f) :
    IsFiniteLength R M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_injective f hf, isArtinian_of_injective f hf⟩
/-
**IsFiniteLength.of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsFiniteLength.of_surjective (H : IsFiniteLength R M) (hf : Function.Surje
ctive f) : IsFiniteLength R N
参数：H : IsFiniteLength R M；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
· 使用定理 `isNoetherian_of_surjective`：isNoetherian_of_surjective {σ : R ->+* S} [R
ingHomSurjective σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian
 R M] : IsNoethe…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `isArtinian_of_surjective`：isArtinian_of_surjective (f : M ->ₗ[R] P) (hf 
: Function.Surjective f) [IsArtinian R M] : IsArtinian R P
-/
lemma IsFiniteLength.of_surjective (H : IsFiniteLength R M) (hf : Function.Surjective f) :
    IsFiniteLength R N := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_surjective f (LinearMap.range_eq_top.mpr hf),
    isArtinian_of_surjective _ f hf⟩

/- The following instances are now automatic:
example [IsSemisimpleRing R] : IsNoetherianRing R := inferInstance
example [IsSemisimpleRing R] : IsArtinianRing R := inferInstance
-/

