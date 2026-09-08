/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Finitely presented algebras and finitely presented modules

In this file we establish relations between finitely presented as an algebra and
finitely presented as a module.

## Main results:

- `Algebra.FinitePresentation.of_finitePresentation`: If `S` is finitely presented as a
  module over `R`, then it is finitely presented as an algebra over `R`.
- `Module.FinitePresentation.of_finite_of_finitePresentation`: If `S` is finite as a module over `R`
  and finitely presented as an algebra over `R`, then it is finitely presented as a module over `R`.

## References

- [Grothendieck, EGA IV₁ 1.4.7][ega-iv-1]
-/

public section

universe u

variable (R : Type u) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- EGA IV₁, 1.4.7.1 -/
/-
**Module.Finite.exists_free_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Finite.exists_free_surjective [Module.Finite R S] : exists (S' : Ty
pe u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S') (_ : Module.
Free R S') (_ : Algebra.FinitePresentation R S') (f : S' ->ₐ[R] S), Function.Sur
jective f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Polynomial.Monic.finite_adjoinRoot`：∀ {R : Type u_1} [inst : CommRing R]
 {g : Polynomial R}, g.Monic → Module.Finite R (AdjoinRoot g)
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.Monic.free_adjoinRoot`：∀ {R : Type u_1} [inst : CommRing R] {
g : Polynomial R}, g.Monic → Module.Free R (AdjoinRoot g)
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用定理 `AdjoinRoot.instIsScalarTower`：∀ {R : Type u_1} [inst : CommRing R] (R₁ :
 Type u_6) (R₂ : Type u_7) [inst_1 : SMul R₁ R₂] [inst_2 : DistribSMul R₁ R]   [
inst_3 : DistribSM…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Module.Free.trans`：Module.Free.trans {R S M : Type*} [CommSemiring R] [S
emiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTo
wer R S…
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用引理 `AdjoinRoot.liftAlgHom_root`：liftAlgHom_root (i : R ->ₐ[S] T) (x : T) (h)
 : liftAlgHom p i x h (root p) = x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AdjoinRoot.liftAlgHom_of`：liftAlgHom_of (i : R ->ₐ[S] T) (x : T) (h) (r 
: R) : liftAlgHom p i x h (of p r) = i r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
EGA IV₁, 1.4.7.1
-/
lemma Module.Finite.exists_free_surjective [Module.Finite R S] :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S')
      (_ : Module.Free R S') (_ : Algebra.FinitePresentation R S')
      (f : S' →ₐ[R] S), Function.Surjective f := by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
  suffices h : ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S')
      (_ : Module.Free R S') (_ : Algebra.FinitePresentation R S')
      (f : S' →ₐ[R] S), (s : Set S) ⊆ AlgHom.range f by
    obtain ⟨S', _, _, _, _, _, f, hsf⟩ := h
    have hf : Function.Surjective f := by
      have := (Submodule.span_le (p := LinearMap.range f.toLinearMap)).mpr hsf
      rwa [hs, top_le_iff, LinearMap.range_eq_top] at this
    use S', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, f
  clear hs
  induction s using Finset.induction with
  | empty =>
    exact ⟨R, _, _, inferInstance, inferInstance, inferInstance, Algebra.ofId R S, by simp⟩
  | insert a s has IH =>
    obtain ⟨S', _, _, _, _, _, f, hsf⟩ := IH
    have ha := Algebra.IsIntegral.isIntegral (R := R) a
    have := ((minpoly.monic ha).map (algebraMap R S')).finite_adjoinRoot
    have := ((minpoly.monic ha).map (algebraMap R S')).free_adjoinRoot
    algebraize [f.toRingHom]
    refine ⟨AdjoinRoot ((minpoly R a).map (algebraMap R S')), inferInstance, inferInstance,
      .trans S' _, .trans (S := S'), .trans _ S' _,
      (AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) a
        (by simp [← Polynomial.aeval_def])).restrictScalars R, ?_⟩
    simp only [Finset.coe_insert, AlgHom.coe_range, AlgHom.coe_restrictScalars',
      Set.insert_subset_iff, Set.mem_range]
    exact ⟨⟨.root _, by simp⟩, hsf.trans fun y ⟨x, hx⟩ ↦ ⟨.of _ x, by simpa⟩⟩

/-- If `S` is finitely presented as a module over `R`, it is finitely
presented as an algebra over `R`. -/
/-
**Algebra.FinitePresentation.of_finitePresentation** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.FinitePresentation.of_finitePresentation [Module.FinitePresentatio
n R S] : Algebra.FinitePresentation R S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_free_surjective`：Module.Finite.exists_free_surjecti
ve [Module.Finite R S] : exists (S' : Type u) (_ : CommRing S') (_ : Algebra R S
') (_ : Module.Finite R S'…
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
· 使用定理 `Algebra.FinitePresentation.of_surjective`：of_surjective {f : A ->ₐ[R] B}
 (hf : Function.Surjective f) (hker : (RingHom.ker f.toRingHom).FG) [FinitePrese
ntation R A] : FinitePresentat…
· 使用定理 `Submodule.FG.of_restrictScalars`：∀ {A : Type u_5} {M : Type u_6} [inst :
 Semiring A] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module A M]   {S : Subm
odule A M} (R : Type …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Module.FinitePresentation.fg_ker`：Module.FinitePresentation.fg_ker [Modu
le.Finite R M] [h : Module.FinitePresentation R N] (l : M ->ₗ[R] N) (hl : Functi
on.Surjective l) : (Li…

--- 原说明 ---
If `S` is finitely presented as a module over `R`, it is finitely
presented as an algebra over `R`.
-/
instance Algebra.FinitePresentation.of_finitePresentation
    [Module.FinitePresentation R S] : Algebra.FinitePresentation R S := by
  obtain ⟨S', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  refine .of_surjective hf ?_
  apply Submodule.FG.of_restrictScalars R
  exact Module.FinitePresentation.fg_ker f.toLinearMap hf

/-- If `S` is finite as a module over `R` and finitely presented as an algebra over `R`, then
it is finitely presented as a module over `R`. -/
@[stacks 0564 "The case M = S"]
/-
**Module.FinitePresentation.of_finite_of_finitePresentation** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：Module.FinitePresentation.of_finite_of_finitePresentation [Module.Finite R
 S] [Algebra.FinitePresentation R S] : Module.FinitePresentation R S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_free_surjective`：Module.Finite.exists_free_surjecti
ve [Module.Finite R S] : exists (S' : Type u) (_ : CommRing S') (_ : Algebra R S
') (_ : Module.Finite R S'…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用引理 `Module.finitePresentation_of_projective`：Module.finitePresentation_of_pr
ojective [Projective R M] [Module.Finite R M] : FinitePresentation R M
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用引理 `Module.finitePresentation_of_surjective`：Module.finitePresentation_of_su
rjective [h : Module.FinitePresentation R M] (l : M ->ₗ[R] N) (hl : Function.Sur
jective l) (hl' : (LinearMap.…
· 使用定理 `instFinitePresentation`：∀ {R : Type u_1} [inst : Ring R], Module.FiniteP
resentation R R
· 使用定理 `Algebra.FinitePresentation.ker_fG_of_surjective`：ker_fG_of_surjective (f
 : A ->ₐ[R] B) (hf : Function.Surjective f) [FinitePresentation R A] [FinitePres
entation R B] : (RingHom.ker f.toRing…
· 使用引理 `Module.FinitePresentation.trans`：Module.FinitePresentation.trans (S : Ty
pe*) [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finit
ePresentation R S] [M…

--- 原说明 ---
If `S` is finite as a module over `R` and finitely presented as an algebra over 
`R`, then
it is finitely presented as a module over `R`.
-/
lemma Module.FinitePresentation.of_finite_of_finitePresentation
    [Module.Finite R S] [Algebra.FinitePresentation R S] :
    Module.FinitePresentation R S := by
  obtain ⟨R', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  let := f.toRingHom.toAlgebra
  have : IsScalarTower R R' S := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.FinitePresentation R R' :=
    Module.finitePresentation_of_projective R R'
  have : Module.FinitePresentation R' S :=
    Module.finitePresentation_of_surjective (Algebra.linearMap R' S) hf
      (Algebra.FinitePresentation.ker_fG_of_surjective f hf)
  exact .trans R S R'

/-- If `S` is a finite `R`-algebra, finitely presented as a module and as an algebra
is equivalent. -/
/-
**Module.FinitePresentation.iff_finitePresentation_of_finite** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：Module.FinitePresentation.iff_finitePresentation_of_finite [Module.Finite 
R S] : Module.FinitePresentation R S ↔ Algebra.FinitePresentation R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.FinitePresentation.of_finite_of_finitePresentation`：Module.Finite
Presentation.of_finite_of_finitePresentation [Module.Finite R S] [Algebra.Finite
Presentation R S] : Module.FinitePresentation R…

--- 原说明 ---
If `S` is a finite `R`-algebra, finitely presented as a module and as an algebra
is equivalent.
-/
lemma Module.FinitePresentation.iff_finitePresentation_of_finite [Module.Finite R S] :
    Module.FinitePresentation R S ↔ Algebra.FinitePresentation R S :=
  ⟨fun _ ↦ .of_finitePresentation R S, fun _ ↦ .of_finite_of_finitePresentation R S⟩
