/-
Copyright (c) 2025 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHomProperties

/-!
# The category of finitely generated `R`-algebras

We define the category of finitely generated `R`-algebras and show it is essentially small.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

variable (R : Type u) [CommRing R]

/-- The category of finitely generated `R`-algebras. -/
/-
**FGAlgCat** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FGAlgCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finitely generated `R`-algebras.
-/
abbrev FGAlgCat := ObjectProperty.FullSubcategory
  fun A : CommAlgCat.{v, u} R ↦ Algebra.FiniteType R A
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : FGAlgCat R) : Algebra.FiniteType R A.1 := A.2

/-- (Implementation detail): A small skeleton of `FGAlgCat`. -/
/-
**FGAlgCatSkeleton** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [CommRing R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail): A small skeleton of `FGAlgCat`.
-/
structure FGAlgCatSkeleton : Type u where
  /-- The number of generators. -/
  n : ℕ
  /-- The defining ideal. -/
  I : Ideal (MvPolynomial (Fin n) R)

/-- (Implementation detail): Realisation of a `FGAlgCatSkeleton`. -/
/-
**FGAlgCatSkeleton.eval** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FGAlgCatSkeleton.eval (A : FGAlgCatSkeleton R) : FGAlgCat.{u} R
参数：A : FGAlgCatSkeleton R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail): Realisation of a `FGAlgCatSkeleton`.
-/
noncomputable def FGAlgCatSkeleton.eval (A : FGAlgCatSkeleton R) : FGAlgCat.{u} R :=
  ⟨CommAlgCat.of R (MvPolynomial (Fin A.n) R ⧸ A.I), inferInstanceAs <| Algebra.FiniteType _ _⟩
/-
**Algebra.FiniteType.exists_fgAlgCatSkeleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.FiniteType.exists_fgAlgCatSkeleton (A : Type v) [CommRing A] [Alge
bra R A] [h : Algebra.FiniteType R A] : exists (P : FGAlgCatSkeleton R), Nonempt
y (A ≃ₐ[R] P.eval.obj)
参数：A : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial''`：iff_quotient_mvPolynomia
l'' : FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), S
urjective f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
-/
lemma Algebra.FiniteType.exists_fgAlgCatSkeleton (A : Type v) [CommRing A] [Algebra R A]
    [h : Algebra.FiniteType R A] :
    ∃ (P : FGAlgCatSkeleton R), Nonempty (A ≃ₐ[R] P.eval.obj) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
  exact ⟨⟨n, RingHom.ker f⟩, ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm⟩⟩
/-
**RingHom.FiniteType.exists_smallRepr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.FiniteType.exists_smallRepr {S : Type v} [CommRing S] {f : R ->+* 
S} (hf : f.FiniteType) : exists (T : FGAlgCatSkeleton R) (e : T.eval.obj ≃+* S),
 f = e.toRingHom.comp (algebraMap _ _)
参数：hf : f.FiniteType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FiniteType.exists_fgAlgCatSkeleton`：Algebra.FiniteType.exists_fg
AlgCatSkeleton (A : Type v) [CommRing A] [Algebra R A] [h : Algebra.FiniteType R
 A] : exists (P : FGAlgCatSkelet…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
-/
lemma RingHom.FiniteType.exists_smallRepr {S : Type v} [CommRing S] {f : R →+* S}
    (hf : f.FiniteType) :
    ∃ (T : FGAlgCatSkeleton R) (e : T.eval.obj ≃+* S), f = e.toRingHom.comp (algebraMap _ _) := by
  algebraize [f]
  obtain ⟨T, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R S
  exact ⟨T, e.symm.toRingEquiv, e.symm.toAlgHom.comp_algebraMap.symm⟩

/-- Universe lift functor for finitely generated algebras. -/
/-
**FGAlgCat.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FGAlgCat.uliftFunctor : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universe lift functor for finitely generated algebras.
-/
def FGAlgCat.uliftFunctor : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R where
  obj A := ⟨.of R <| ULift A.1, .equiv inferInstance ULift.algEquiv.symm⟩
  map {A B} f := ConcreteCategory.ofHom <|
    ULift.algEquiv.symm.toAlgHom.comp <| f.hom.hom.comp ULift.algEquiv.toAlgHom

/-- The universe lift functor for finitely generated algebras is fully faithful. -/
/-
**FGAlgCat.fullyFaithfulUliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FGAlgCat.fullyFaithfulUliftFunctor : (FGAlgCat.uliftFunctor R).FullyFaithf
ul where preimage {A B} f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universe lift functor for finitely generated algebras is fully faithful.
-/
def FGAlgCat.fullyFaithfulUliftFunctor : (FGAlgCat.uliftFunctor R).FullyFaithful where
  preimage {A B} f :=
    ConcreteCategory.ofHom <| ULift.algEquiv.toAlgHom.comp <|
      f.hom.hom.comp ULift.algEquiv.symm.toAlgHom
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (FGAlgCat.uliftFunctor R).Full :=
  (FGAlgCat.fullyFaithfulUliftFunctor R).full
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (FGAlgCat.uliftFunctor R).Faithful :=
  (FGAlgCat.fullyFaithfulUliftFunctor R).faithful

/-- The category of finitely generated algebras is essentially small. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finitely generated algebras is essentially small.
-/
instance : EssentiallySmall.{u} (FGAlgCat.{v} R) := by
  suffices h : EssentiallySmall.{u} (FGAlgCat.{max u v} R) by
    exact essentiallySmall_of_fully_faithful (FGAlgCat.uliftFunctor R)
  rw [essentiallySmall_iff]
  refine ⟨?_, ?_⟩
  · let f := toSkeleton ∘ (FGAlgCat.uliftFunctor R).obj ∘ FGAlgCatSkeleton.eval R
    refine small_of_surjective (f := f) fun A ↦ ?_
    simp only [Function.comp_apply, f, toSkeleton_eq_iff]
    obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R
      ((fromSkeleton (FGAlgCat R)).obj A).obj
    exact ⟨P, ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk <| ULift.algEquiv.trans e.symm)⟩⟩
  · refine ⟨fun A B ↦ ?_⟩
    obtain ⟨PA, ⟨eA⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R A.obj
    obtain ⟨PB, ⟨eB⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R B.obj
    let f (g : A ⟶ B) (x : PA.eval.obj) : PB.eval.obj := eB (g.hom (eA.symm x))
    refine small_of_injective (f := f) fun u v h ↦ ?_
    ext a
    obtain ⟨a, rfl⟩ := eA.symm.surjective a
    exact eB.injective (congr_fun h a)

section Under

open RingHom

/-- The category of finitely generated `R`-algebras is equivalent to the category of
finite type ring homomorphisms from `R`. -/
/-
**FGAlgCat.equivUnder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FGAlgCat.equivUnder (R : CommRingCat.{u}) : FGAlgCat R ≌ MorphismProperty.
Under (toMorphismProperty FiniteType) ⊤ R where functor.obj A
参数：R : CommRingCat.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `trivial`：True

--- 原说明 ---
The category of finitely generated `R`-algebras is equivalent to the category of
finite type ring homomorphisms from `R`.
-/
def FGAlgCat.equivUnder (R : CommRingCat.{u}) :
    FGAlgCat R ≌ MorphismProperty.Under (toMorphismProperty FiniteType) ⊤ R where
  functor.obj A := ⟨(commAlgCatEquivUnder R).functor.obj A.obj,
    (RingHom.finiteType_algebraMap (A := R) (B := A.obj)).mpr A.2⟩
  functor.map {A B} f := ⟨(commAlgCatEquivUnder R).functor.map f.hom, trivial, trivial⟩
  inverse.obj A := ⟨(commAlgCatEquivUnder R).inverse.obj A.1, A.2⟩
  inverse.map {A B} f := ObjectProperty.homMk ((commAlgCatEquivUnder R).inverse.map f.hom)
  unitIso := NatIso.ofComponents fun A ↦
    ObjectProperty.isoMk _ (CommAlgCat.isoMk { toRingEquiv := .refl A.1, commutes' _ := rfl })
  counitIso := .refl _

variable {Q : MorphismProperty CommRingCat.{u}}
/-
**essentiallySmall_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：essentiallySmall_of_le (hQ : Q <= toMorphismProperty FiniteType) (R : Comm
RingCat.{u}) : EssentiallySmall.{u} (MorphismProperty.Under Q ⊤ R)
参数：hQ : Q <= toMorphismProperty FiniteType；R : CommRingCat.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.essentiallySmall_of_fully_faithful`：essentiallySmall_of_f
ully_faithful {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful] 
[EssentiallySmall.{w} D] : EssentiallyS…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `CategoryTheory.Functor.Full.comp`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.instFullChangeProp`：∀ {A : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `CategoryTheory.Functor.Faithful.comp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.instFaithfulChangeProp`：∀ {A : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `instEssentiallySmallFGAlgCat`：∀ (R : Type u) [inst : CommRing R], Catego
ryTheory.EssentiallySmall.{u, v, max (v + 1) u} (FGAlgCat R)
-/
lemma essentiallySmall_of_le (hQ : Q ≤ toMorphismProperty FiniteType) (R : CommRingCat.{u}) :
    EssentiallySmall.{u} (MorphismProperty.Under Q ⊤ R) :=
  essentiallySmall_of_fully_faithful
    (MorphismProperty.Comma.changeProp _ _ hQ
      le_rfl le_rfl ⋙ (FGAlgCat.equivUnder R).inverse)

end Under

