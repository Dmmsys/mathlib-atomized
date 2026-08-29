/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Small.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Injective modules

## Main definitions

* `Module.Injective`: an `R`-module `Q` is injective if and only if every injective `R`-linear
  map descends to a linear map to `Q`, i.e. in the following diagram, if `f` is injective then there
  is an `R`-linear map `h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
* `Module.Baer`: an `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an
  `Ideal R` extends to an `R`-linear map `R ⟶ Q`

## Main statements

* `Module.Baer.injective`: an `R`-module is injective if it is Baer.

-/

@[expose] public section

assert_not_exists ModuleCat

noncomputable section

universe u v v'

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

/--
Definition of `Module.Injective` / `Module.Injective` 的定义

English:
class Module.Injective
  parameters: : Prop where
  axioms and operations (1):
    - out : forall ⦃X Y : Type v⦄ [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y] (f : X ->ₗ[R] Y) (_ : Function.Injective f) (g : X ->ₗ[R] Q), exists h : Y ->ₗ[R] Q, forall x, h (f x) = g x

中文:
类 Module.Injective
  参数: : 命题 where
  公理与运算 (1 个):
    - out : 对任意 ⦃X Y : 类型v⦄ [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y] (f : X ->ₗ[R] Y) (_ : Function.Injective f) (g : X ->ₗ[R] Q), 存在 h : Y ->ₗ[R] Q, 对任意 x, h (f x) = g x

Depends on / 依赖: Module, torsionBy
-/
@[mk_iff] class Module.Injective : Prop where
  out : forall ⦃X Y : Type v⦄ [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
    (f : X ->ₗ[R] Y) (_ : Function.Injective f) (g : X ->ₗ[R] Q),
    exists h : Y ->ₗ[R] Q, forall x, h (f x) = g x

/--
Definition of `Module.Baer` / `Module.Baer` 的定义

English:
definition Module.Baer
  signature: : Prop
  body: forall (I : Ideal R) (g : I ->ₗ[R] Q), exists g' : R ->ₗ[R] Q, forall (x : R) (mem : x in I), g' x = g ⟨x, mem⟩

中文:
定义 Module.Baer
  签名: : 命题
  定义体: forall (I : Ideal R) (g : I ->ₗ[R] Q), exists g' : R ->ₗ[R] Q, forall (x : R) (mem : x in I), g' x = g ⟨x, mem⟩
-/
def Module.Baer : Prop :=
  forall (I : Ideal R) (g : I ->ₗ[R] Q), exists g' : R ->ₗ[R] Q, forall (x : R) (mem : x in I), g' x = g ⟨x, mem⟩

namespace Module.Baer

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] (i : M ->ₗ[R] N) (f : M ->ₗ[R] Q)

/--
lemma `of_equiv` / 引理 `of_equiv`

English:
lemma of_equiv
  given: (e : Q ≃ₗ[R] M) (h : Module.Baer R Q)
  statement: Module.Baer R M
  proof: fun I g =>
  have ⟨g', h'⟩ := h I (e.symm ∘ₗ g)
  ⟨e ∘ₗ g', by simpa [LinearEquiv.eq_symm_apply] using h'⟩

中文:
引理 of_equiv
  条件: (e : Q ≃ₗ[R] M) (h : Module.Baer R Q)
  结论: Module.Baer R M
  证明: fun I g =>
  have ⟨g', h'⟩ := h I (e.symm ∘ₗ g)
  ⟨e ∘ₗ g', by simpa [LinearEquiv.eq_symm_apply] using h'⟩
-/
lemma of_equiv (e : Q ≃ₗ[R] M) (h : Module.Baer R Q) : Module.Baer R M := fun I g =>
  have ⟨g', h'⟩ := h I (e.symm ∘ₗ g)
  ⟨e ∘ₗ g', by simpa [LinearEquiv.eq_symm_apply] using h'⟩

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: (e : Q ≃ₗ[R] M)
  statement: Module.Baer R Q ↔ Module.Baer R M
  proof: ⟨of_equiv e, of_equiv e.symm⟩

中文:
引理 congr
  条件: (e : Q ≃ₗ[R] M)
  结论: Module.Baer R Q ↔ Module.Baer R M
  证明: ⟨of_equiv e, of_equiv e.symm⟩

Depends on / 依赖: e.symm, of_equiv
-/
lemma congr (e : Q ≃ₗ[R] M) : Module.Baer R Q ↔ Module.Baer R M := ⟨of_equiv e, of_equiv e.symm⟩

/--
lemma `iff_surjective` / 引理 `iff_surjective`

English:
lemma iff_surjective
  given: {R : Type u} [CommRing R] [Module R M]
  statement: Module.Baer R M ↔
  proof: by
  refine ⟨fun h I g => ?_, fun h I g => ?_⟩
  · rcases h I g with ⟨g', hg'⟩
    use g'
    ext x
    simp [hg']
  · rcases h I g with ⟨g', hg'⟩
    use g'
    intro x hx
    simp [← hg']

中文:
引理 iff_surjective
  条件: {R : 类型u} [CommRing R] [Module R M]
  结论: Module.Baer R M ↔
  证明: by
  refine ⟨fun h I g => ?_, fun h I g => ?_⟩
  · rcases h I g with ⟨g', hg'⟩
    use g'
    ext x
    simp [hg']
  · rcases h I g with ⟨g', hg'⟩
    use g'
    intro x hx
    simp [← hg']
-/
lemma iff_surjective {R : Type u} [CommRing R] [Module R M] : Module.Baer R M ↔
    forall (I : Ideal R), Function.Surjective (LinearMap.lcomp R M I.subtype) := by
  refine ⟨fun h I g => ?_, fun h I g => ?_⟩
  · rcases h I g with ⟨g', hg'⟩
    use g'
    ext x
    simp [hg']
  · rcases h I g with ⟨g', hg'⟩
    use g'
    intro x hx
    simp [← hg']

/--
Definition of `ExtensionOf` / `ExtensionOf` 的定义

English:
structure ExtensionOf
  parameters: extends N ->ₗ.[R] Q
  extends: N ->ₗ.[R] Q
  axioms and operations (2):
    - le : LinearMap.range i <= domain
    - is_extension : forall m : M, f m = toLinearPMap ⟨i m, le ⟨m, rfl⟩⟩

中文:
结构 ExtensionOf
  参数: extends N ->ₗ.[R] Q
  继承: N ->ₗ.[R] Q
  公理与运算 (2 个):
    - le : LinearMap.range i <= domain
    - is_extension : 对任意 m : M, f m = toLinearPMap ⟨i m, le ⟨m, rfl⟩⟩

Depends on / 依赖: Finite, Module, Module.Finite.of_restrictScalars_finite, of_restrictScalars_finite
-/
structure ExtensionOf extends N ->ₗ.[R] Q where
  le : LinearMap.range i <= domain
  is_extension : forall m : M, f m = toLinearPMap ⟨i m, le ⟨m, rfl⟩⟩

section Ext

variable {i f}

@[ext (iff := false)]
/--
theorem `ExtensionOf.ext` / 定理 `ExtensionOf.ext`

English:
theorem ExtensionOf.ext
  statement: {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
  proof: by
  rcases a with ⟨a, a_le, e1⟩
  congr
  exact LinearPMap.ext domain_eq to_fun_eq

中文:
定理 ExtensionOf.ext
  结论: {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
  证明: by
  rcases a with ⟨a, a_le, e1⟩
  congr
  exact LinearPMap.ext domain_eq to_fun_eq

Depends on / 依赖: LinearPMap, LinearPMap.ext, a_le, domain_eq, to_fun_eq
-/
theorem ExtensionOf.ext {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
    (to_fun_eq : forall ⦃x : N⦄ ⦃ha : x in a.domain⦄ ⦃hb : x in b.domain⦄,
      a.toLinearPMap ⟨x, ha⟩ = b.toLinearPMap ⟨x, hb⟩) :
    a = b := by
  rcases a with ⟨a, a_le, e1⟩
  congr
  exact LinearPMap.ext domain_eq to_fun_eq

/--
theorem `ExtensionOf.dExt` / 定理 `ExtensionOf.dExt`

English:
theorem ExtensionOf.dExt
  statement: {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
  proof: ext domain_eq fun _ _ _ => to_fun_eq rfl

中文:
定理 ExtensionOf.dExt
  结论: {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
  证明: ext domain_eq fun _ _ _ => to_fun_eq rfl

Depends on / 依赖: domain_eq, to_fun_eq
-/
theorem ExtensionOf.dExt {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
    (to_fun_eq :
      forall ⦃x : a.domain⦄ ⦃y : b.domain⦄, (x : N) = y -> a.toLinearPMap x = b.toLinearPMap y) :
    a = b :=
  ext domain_eq fun _ _ _ => to_fun_eq rfl

/--
theorem `ExtensionOf.dExt_iff` / 定理 `ExtensionOf.dExt_iff`

English:
theorem ExtensionOf.dExt_iff
  given: {a b : ExtensionOf i f}
  proof: ⟨fun r => r ▸ ⟨rfl, fun _ _ h => congr_arg a.toFun mod_cast h⟩, fun ⟨h1, h2⟩ =>
    ExtensionOf.dExt h1 h2⟩

中文:
定理 ExtensionOf.dExt_iff
  条件: {a b : ExtensionOf i f}
  证明: ⟨fun r => r ▸ ⟨rfl, fun _ _ h => congr_arg a.toFun mod_cast h⟩, fun ⟨h1, h2⟩ =>
    ExtensionOf.dExt h1 h2⟩

Depends on / 依赖: ExtensionOf, ExtensionOf.dExt, a.toFun, congr_arg, mod_cast
-/
theorem ExtensionOf.dExt_iff {a b : ExtensionOf i f} :
    a = b ↔ exists _ : a.domain = b.domain, forall ⦃x : a.domain⦄ ⦃y : b.domain⦄,
    (x : N) = y -> a.toLinearPMap x = b.toLinearPMap y :=
⟨fun r => r ▸ ⟨rfl, fun _ _ h => congr_arg a.toFun mod_cast h⟩, fun ⟨h1, h2⟩ =>
    ExtensionOf.dExt h1 h2⟩

/--
theorem `ExtensionOf.toLinearPMap_injective` / 定理 `ExtensionOf.toLinearPMap_injective`

English:
theorem ExtensionOf.toLinearPMap_injective
  proof: fun _ _ _ => by ext <;> congr!

中文:
定理 ExtensionOf.toLinearPMap_injective
  证明: fun _ _ _ => by ext <;> congr!

Depends on / 依赖: ExtensionOf, ExtensionOf.toLinearPMap, toLinearPMap
-/
theorem ExtensionOf.toLinearPMap_injective :
    Function.Injective (α := ExtensionOf i f) ExtensionOf.toLinearPMap :=
  fun _ _ _ => by ext <;> congr!

end Ext

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (ExtensionOf i f)
  body: { X1.toLinearPMap ⊓ X2.toLinearPMap with
      le := fun x hx =>
        (by
          rcases hx with ⟨x, rfl⟩
          refine ⟨X1.le (Set.mem_range_self _), X2.le (Set.mem_range_self _), ?_⟩
          rw [← X1.is_extension x]; rw [← X2.is_extension x] :
          x in X1.toLinearPMap.eqLocus X2.to

中文:
实例 :
  签名: Min (ExtensionOf i f)
  定义体: { X1.toLinearPMap ⊓ X2.toLinearPMap with
      le := fun x hx =>
        (by
          rcases hx with ⟨x, rfl⟩
          refine ⟨X1.le (Set.mem_range_self _), X2.le (Set.mem_range_self _), ?_⟩
          rw [← X1.is_extension x]; rw [← X2.is_extension x] :
          x in X1.toLinearPMap.eqLocus X2.to

Depends on / 依赖: Set.mem_range_self, X1.is_extension, X1.le, X1.toLinearPMap, X1.toLinearPMap.eqLocus, X2.is_extension, X2.le, X2.toLinearPMap, eqLocus, is_extension, mem_range_self, toLinearPMap
-/
instance : Min (ExtensionOf i f) where
  min X1 X2 :=
    { X1.toLinearPMap ⊓ X2.toLinearPMap with
      le := fun x hx =>
        (by
          rcases hx with ⟨x, rfl⟩
          refine ⟨X1.le (Set.mem_range_self _), X2.le (Set.mem_range_self _), ?_⟩
          rw [← X1.is_extension x]; rw [← X2.is_extension x] :
          x in X1.toLinearPMap.eqLocus X2.toLinearPMap)
      is_extension := fun _ => X1.is_extension _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (ExtensionOf i f)
  body: PartialOrder.lift _ ExtensionOf.toLinearPMap_injective

中文:
实例 :
  签名: PartialOrder (ExtensionOf i f)
  定义体: PartialOrder.lift _ ExtensionOf.toLinearPMap_injective

Depends on / 依赖: ExtensionOf, ExtensionOf.toLinearPMap_injective, PartialOrder, PartialOrder.lift, toLinearPMap_injective
-/
instance : PartialOrder (ExtensionOf i f) :=
  PartialOrder.lift _ ExtensionOf.toLinearPMap_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (ExtensionOf i f)
  body: ExtensionOf.toLinearPMap_injective.semilatticeInf _
    .rfl .rfl fun X Y => LinearPMap.ext rfl fun x y h => by congr

中文:
实例 :
  签名: SemilatticeInf (ExtensionOf i f)
  定义体: ExtensionOf.toLinearPMap_injective.semilatticeInf _
    .rfl .rfl fun X Y => LinearPMap.ext rfl fun x y h => by congr

Depends on / 依赖: ExtensionOf, ExtensionOf.toLinearPMap_injective.semilatticeInf, LinearPMap, LinearPMap.ext, Subtype, Subtype.ext, semilatticeInf, toLinearPMap_injective
-/
instance : SemilatticeInf (ExtensionOf i f) :=
  ExtensionOf.toLinearPMap_injective.semilatticeInf _
    .rfl .rfl fun X Y => LinearPMap.ext rfl fun x y h => by congr

variable {i f}

/--
theorem `chain_linearPMap_of_chain_extensionOf` / 定理 `chain_linearPMap_of_chain_extensionOf`

English:
theorem chain_linearPMap_of_chain_extensionOf
  statement: {c : Set (ExtensionOf i f)}
  proof: by
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ ne
  exact hchain a_mem b_mem (ne_of_apply_ne _ ne)

中文:
定理 chain_linearPMap_of_chain_extensionOf
  结论: {c : Set (ExtensionOf i f)}
  证明: by
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ ne
  exact hchain a_mem b_mem (ne_of_apply_ne _ ne)

Depends on / 依赖: _eq_top, _iff_torsion, _isTorsion, a_mem, b_mem, hchain, isTorsion, ne_of_apply_ne, torsion
-/
theorem chain_linearPMap_of_chain_extensionOf {c : Set (ExtensionOf i f)}
    (hchain : IsChain (· <= ·) c) :
IsChain (· <= ·) (fun x : ExtensionOf i f => x.toLinearPMap) '' c := by
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ ne
  exact hchain a_mem b_mem (ne_of_apply_ne _ ne)

/--
Definition of `ExtensionOf.max` / `ExtensionOf.max` 的定义

English:
definition ExtensionOf.max
  signature: {c : Set (ExtensionOf i f)} (hchain : IsChain (· <= ·) c)
  body: { LinearPMap.sSup _
      (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain) with
    le := by
refine le_trans hnonempty.some.le
        (LinearPMap.le_sSup _ <|
            (Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩).1
    is_extension := fun m => by
  

中文:
定义 ExtensionOf.max
  签名: {c : Set (ExtensionOf i f)} (hchain : IsChain (· <= ·) c)
  定义体: { LinearPMap.sSup _
      (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain) with
    le := by
refine le_trans hnonempty.some.le
        (LinearPMap.le_sSup _ <|
            (Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩).1
    is_extension := fun m => by
  

Depends on / 依赖: Eq.trans, IsChain, IsChain.directedOn, LinearPMap, LinearPMap.le_sSup, LinearPMap.sSup, LinearPMap.sSup_apply, Set.mem_image, chain_linearPMap_of_chain_extensionOf, choose_spec, directedOn, generalize_proofs, hchain, hnonempty, hnonempty.choo, hnonempty.choose_spec, hnonempty.some, hnonempty.some.is_extension, hnonempty.some.le, is_extension
-/
def ExtensionOf.max {c : Set (ExtensionOf i f)} (hchain : IsChain (· <= ·) c)
    (hnonempty : c.Nonempty) : ExtensionOf i f :=
  { LinearPMap.sSup _
      (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain) with
    le := by
refine le_trans hnonempty.some.le
        (LinearPMap.le_sSup _ <|
            (Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩).1
    is_extension := fun m => by
      refine Eq.trans (hnonempty.some.is_extension m) ?_
      symm
      generalize_proofs _ _ h1
      exact
        LinearPMap.sSup_apply (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain)
          ((Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩) ⟨i m, h1⟩ }

/--
theorem `ExtensionOf.le_max` / 定理 `ExtensionOf.le_max`

English:
theorem ExtensionOf.le_max
  statement: {c : Set (ExtensionOf i f)} (hchain : IsChain (· <= ·) c)
  proof: LinearPMap.le_sSup (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain)
    (Set.mem_image _ _ _).mpr ⟨a, ha, rfl⟩

中文:
定理 ExtensionOf.le_max
  结论: {c : Set (ExtensionOf i f)} (hchain : IsChain (· <= ·) c)
  证明: LinearPMap.le_sSup (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain)
    (Set.mem_image _ _ _).mpr ⟨a, ha, rfl⟩

Depends on / 依赖: IsChain, IsChain.directedOn, LinearPMap, LinearPMap.le_sSup, Set.mem_image, chain_linearPMap_of_chain_extensionOf, directedOn, hchain, le_sSup, mem_image
-/
theorem ExtensionOf.le_max {c : Set (ExtensionOf i f)} (hchain : IsChain (· <= ·) c)
    (hnonempty : c.Nonempty) (a : ExtensionOf i f) (ha : a in c) :
    a <= ExtensionOf.max hchain hnonempty :=
LinearPMap.le_sSup (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain)
    (Set.mem_image _ _ _).mpr ⟨a, ha, rfl⟩

variable (i f) [Fact <| Function.Injective i]

/--
Instance `ExtensionOf.inhabited` / 实例 `ExtensionOf.inhabited`

English:
instance ExtensionOf.inhabited
  signature: : Inhabited (ExtensionOf i f) where
  body: { domain := LinearMap.range i
      toFun :=
        { toFun := fun x => f x.2.choose
          map_add' := fun x y => by
            have eq1 : _ + _ = (x + y).1 := congr_arg₂ (· + ·) x.2.choose_spec y.2.choose_spec
            rw [← map_add]; rw [← (x + y).2.choose_spec] at eq1
            dsimp
 

中文:
实例 ExtensionOf.inhabited
  签名: : Inhabited (ExtensionOf i f) where
  定义体: { domain := LinearMap.range i
      toFun :=
        { toFun := fun x => f x.2.choose
          map_add' := fun x y => by
            have eq1 : _ + _ = (x + y).1 := congr_arg₂ (· + ·) x.2.choose_spec y.2.choose_spec
            rw [← map_add]; rw [← (x + y).2.choose_spec] at eq1
            dsimp
 

Depends on / 依赖: Fact.out, Function, Function.Injective, Injective, LinearMap, LinearMap.range, choose_spec, congr_arg, domain, map_add, map_smul
-/
instance ExtensionOf.inhabited : Inhabited (ExtensionOf i f) where
  default :=
    { domain := LinearMap.range i
      toFun :=
        { toFun := fun x => f x.2.choose
          map_add' := fun x y => by
            have eq1 : _ + _ = (x + y).1 := congr_arg₂ (· + ·) x.2.choose_spec y.2.choose_spec
            rw [← map_add]; rw [← (x + y).2.choose_spec] at eq1
            dsimp
            rw [← Fact.out (p := Function.Injective i) eq1]; rw [map_add]
          map_smul' := fun r x => by
            have eq1 : r • _ = (r • x).1 := congr_arg (r • ·) x.2.choose_spec
            rw [← map_smul]; rw [← (r • x).2.choose_spec] at eq1
            dsimp
            rw [← Fact.out (p := Function.Injective i) eq1]; rw [map_smul] }
      le := le_refl _
      is_extension := fun m => by
        simp only [LinearPMap.mk_apply, LinearMap.coe_mk]
        dsimp
        apply congrArg
        exact Fact.out (p := Function.Injective i)
          (⟨i m, ⟨_, rfl⟩⟩ : LinearMap.range i).2.choose_spec.symm }

/--
Definition of `extensionOfMax` / `extensionOfMax` 的定义

English:
definition extensionOfMax
  signature: : ExtensionOf i f
  body: (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
      ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose

中文:
定义 extensionOfMax
  签名: : ExtensionOf i f
  定义体: (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
      ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose

Depends on / 依赖: ExtensionOf, ExtensionOf.le_max, ExtensionOf.max, Inhabited, Inhabited.default, hchain, hnonempty, le_max, zorn_le_nonempty
-/
def extensionOfMax : ExtensionOf i f :=
  (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
      ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose

/--
theorem `extensionOfMax_is_max` / 定理 `extensionOfMax_is_max`

English:
theorem extensionOfMax_is_max
  proof: fun _ => (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
    ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose_spec.eq_of_ge

中文:
定理 extensionOfMax_is_max
  证明: fun _ => (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
    ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose_spec.eq_of_ge

Depends on / 依赖: ExtensionOf, ExtensionOf.le_max, ExtensionOf.max, Inhabited, Inhabited.default, choose_spec, choose_spec.eq_of_ge, eq_of_ge, hchain, hnonempty, le_max, zorn_le_nonempty
-/
theorem extensionOfMax_is_max :
    forall (a : ExtensionOf i f), extensionOfMax i f <= a -> a = extensionOfMax i f :=
  fun _ => (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
    ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose_spec.eq_of_ge

-- Auxiliary definition: Lean looks for an instance of `Max (Type u)` if we would write
-- `(x : (extensionOfMax i f).domain ⊔ (Submodule.span R {y}))`, so we encapsulate the cast instead.
/--
Definition of `supExtensionOfMaxSingleton` / `supExtensionOfMaxSingleton` 的定义

English:
abbreviation supExtensionOfMaxSingleton
  signature: (y : N)
  body: (extensionOfMax i f).domain ⊔ (Submodule.span R {y})

中文:
缩写 supExtensionOfMaxSingleton
  签名: (y : N)
  定义体: (extensionOfMax i f).domain ⊔ (Submodule.span R {y})

Depends on / 依赖: Submodule, Submodule.span, domain, extensionOfMax
-/
abbrev supExtensionOfMaxSingleton (y : N) : Submodule R N :=
  (extensionOfMax i f).domain ⊔ (Submodule.span R {y})

variable {f}

set_option backward.privateInPublic true in
/--
theorem `extensionOfMax_adjoin.aux1` / 定理 `extensionOfMax_adjoin.aux1`

English:
theorem extensionOfMax_adjoin.aux1
  given: {y : N} (x : supExtensionOfMaxSingleton i f y)
  proof: by
  have mem1 : x.1 in (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, a_mem, b, b_mem : b in (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩

中文:
定理 extensionOfMax_adjoin.aux1
  条件: {y : N} (x : supExtensionOfMaxSingleton i f y)
  证明: by
  have mem1 : x.1 in (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, a_mem, b, b_mem : b in (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩
-/
private theorem extensionOfMax_adjoin.aux1 {y : N} (x : supExtensionOfMaxSingleton i f y) :
    exists (a : (extensionOfMax i f).domain) (b : R), x.1 = a.1 + b • y := by
  have mem1 : x.1 in (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, a_mem, b, b_mem : b in (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `ExtensionOfMaxAdjoin.fst` / `ExtensionOfMaxAdjoin.fst` 的定义

English:
definition ExtensionOfMaxAdjoin.fst
  signature: {y : N} (x : supExtensionOfMaxSingleton i f y)
  body: (extensionOfMax_adjoin.aux1 i x).choose

中文:
定义 ExtensionOfMaxAdjoin.fst
  签名: {y : N} (x : supExtensionOfMaxSingleton i f y)
  定义体: (extensionOfMax_adjoin.aux1 i x).choose

Depends on / 依赖: extensionOfMax_adjoin, extensionOfMax_adjoin.aux1
-/
def ExtensionOfMaxAdjoin.fst {y : N} (x : supExtensionOfMaxSingleton i f y) :
    (extensionOfMax i f).domain :=
  (extensionOfMax_adjoin.aux1 i x).choose

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `ExtensionOfMaxAdjoin.snd` / `ExtensionOfMaxAdjoin.snd` 的定义

English:
definition ExtensionOfMaxAdjoin.snd
  signature: {y : N} (x : supExtensionOfMaxSingleton i f y)
  body: (extensionOfMax_adjoin.aux1 i x).choose_spec.choose

中文:
定义 ExtensionOfMaxAdjoin.snd
  签名: {y : N} (x : supExtensionOfMaxSingleton i f y)
  定义体: (extensionOfMax_adjoin.aux1 i x).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, extensionOfMax_adjoin, extensionOfMax_adjoin.aux1
-/
def ExtensionOfMaxAdjoin.snd {y : N} (x : supExtensionOfMaxSingleton i f y) : R :=
  (extensionOfMax_adjoin.aux1 i x).choose_spec.choose

/--
theorem `ExtensionOfMaxAdjoin.eqn` / 定理 `ExtensionOfMaxAdjoin.eqn`

English:
theorem ExtensionOfMaxAdjoin.eqn
  given: {y : N} (x : supExtensionOfMaxSingleton i f y)
  proof: (extensionOfMax_adjoin.aux1 i x).choose_spec.choose_spec

中文:
定理 ExtensionOfMaxAdjoin.eqn
  条件: {y : N} (x : supExtensionOfMaxSingleton i f y)
  证明: (extensionOfMax_adjoin.aux1 i x).choose_spec.choose_spec

Depends on / 依赖: choose_spec, choose_spec.choose_spec, extensionOfMax_adjoin, extensionOfMax_adjoin.aux1
-/
theorem ExtensionOfMaxAdjoin.eqn {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ↑x = ↑(ExtensionOfMaxAdjoin.fst i x) + ExtensionOfMaxAdjoin.snd i x • y :=
  (extensionOfMax_adjoin.aux1 i x).choose_spec.choose_spec

variable (f)

-- TODO: refactor to use colon ideals?
/--
Definition of `ExtensionOfMaxAdjoin.ideal` / `ExtensionOfMaxAdjoin.ideal` 的定义

English:
definition ExtensionOfMaxAdjoin.ideal
  signature: (y : N)
  body: (extensionOfMax i f).domain.comap ((LinearMap.id : R ->ₗ[R] R).smulRight y)

中文:
定义 ExtensionOfMaxAdjoin.ideal
  签名: (y : N)
  定义体: (extensionOfMax i f).domain.comap ((LinearMap.id : R ->ₗ[R] R).smulRight y)

Depends on / 依赖: LinearMap, LinearMap.id, domain, domain.comap, extensionOfMax, smulRight
-/
def ExtensionOfMaxAdjoin.ideal (y : N) : Ideal R :=
  (extensionOfMax i f).domain.comap ((LinearMap.id : R ->ₗ[R] R).smulRight y)

/--
Definition of `ExtensionOfMaxAdjoin.idealTo` / `ExtensionOfMaxAdjoin.idealTo` 的定义

English:
definition ExtensionOfMaxAdjoin.idealTo
  signature: (y : N)
  body: (extensionOfMax i f).toLinearPMap ⟨(↑z : R) • y, z.prop⟩
  map_add' (z1 z2 : { x // x in ideal i f y }) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_add]
    congr
    apply add_smul
  map_smul' z1 (z2 : {x // x in ideal i f y}) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.ma

中文:
定义 ExtensionOfMaxAdjoin.idealTo
  签名: (y : N)
  定义体: (extensionOfMax i f).toLinearPMap ⟨(↑z : R) • y, z.prop⟩
  map_add' (z1 z2 : { x // x in ideal i f y }) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_add]
    congr
    apply add_smul
  map_smul' z1 (z2 : {x // x in ideal i f y}) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.ma

Depends on / 依赖: extensionOfMax, toLinearPMap, z.prop
-/
def ExtensionOfMaxAdjoin.idealTo (y : N) : ExtensionOfMaxAdjoin.ideal i f y ->ₗ[R] Q where
  toFun (z : { x // x in ideal i f y }) := (extensionOfMax i f).toLinearPMap ⟨(↑z : R) • y, z.prop⟩
  map_add' (z1 z2 : { x // x in ideal i f y }) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_add]
    congr
    apply add_smul
  map_smul' z1 (z2 : {x // x in ideal i f y}) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_smul]
    congr 2
    apply mul_smul

/--
Definition of `ExtensionOfMaxAdjoin.extendIdealTo` / `ExtensionOfMaxAdjoin.extendIdealTo` 的定义

English:
definition ExtensionOfMaxAdjoin.extendIdealTo
  signature: (h : Module.Baer R Q) (y : N)
  body: (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose

中文:
定义 ExtensionOfMaxAdjoin.extendIdealTo
  签名: (h : Module.Baer R Q) (y : N)
  定义体: (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose

Depends on / 依赖: ExtensionOfMaxAdjoin, ExtensionOfMaxAdjoin.ideal, ExtensionOfMaxAdjoin.idealTo, idealTo
-/
def ExtensionOfMaxAdjoin.extendIdealTo (h : Module.Baer R Q) (y : N) : R ->ₗ[R] Q :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose

/--
theorem `ExtensionOfMaxAdjoin.extendIdealTo_is_extension` / 定理 `ExtensionOfMaxAdjoin.extendIdealTo_is_extension`

English:
theorem ExtensionOfMaxAdjoin.extendIdealTo_is_extension
  given: (h : Module.Baer R Q) (y : N)
  proof: (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose_spec

中文:
定理 ExtensionOfMaxAdjoin.extendIdealTo_is_extension
  条件: (h : Module.Baer R Q) (y : N)
  证明: (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose_spec

Depends on / 依赖: ExtensionOfMaxAdjoin, ExtensionOfMaxAdjoin.ideal, ExtensionOfMaxAdjoin.idealTo, choose_spec, idealTo
-/
theorem ExtensionOfMaxAdjoin.extendIdealTo_is_extension (h : Module.Baer R Q) (y : N) :
    forall (x : R) (mem : x in ExtensionOfMaxAdjoin.ideal i f y),
      ExtensionOfMaxAdjoin.extendIdealTo i f h y x = ExtensionOfMaxAdjoin.idealTo i f y ⟨x, mem⟩ :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose_spec

/--
theorem `ExtensionOfMaxAdjoin.extendIdealTo_wd'` / 定理 `ExtensionOfMaxAdjoin.extendIdealTo_wd'`

English:
theorem ExtensionOfMaxAdjoin.extendIdealTo_wd'
  statement: (h : Module.Baer R Q) {y : N} (r : R)
  proof: by
  have : r in ideal i f y := by
    change (r • y) in (extensionOfMax i f).toLinearPMap.domain
    rw [eq1]
    apply Submodule.zero_mem _
  rw [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h y r this]
  dsimp [ExtensionOfMaxAdjoin.idealTo]
  simp only [eq1, ← ZeroMemClass.zero_def, (exten

中文:
定理 ExtensionOfMaxAdjoin.extendIdealTo_wd'
  结论: (h : Module.Baer R Q) {y : N} (r : R)
  证明: by
  have : r in ideal i f y := by
    change (r • y) in (extensionOfMax i f).toLinearPMap.domain
    rw [eq1]
    apply Submodule.zero_mem _
  rw [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h y r this]
  dsimp [ExtensionOfMaxAdjoin.idealTo]
  simp only [eq1, ← ZeroMemClass.zero_def, (exten

Depends on / 依赖: ExtensionOfMaxAdjoin, ExtensionOfMaxAdjoin.extendIdealTo_is_extension, ExtensionOfMaxAdjoin.idealTo, Submodule, Submodule.zero_mem, ZeroMemClass, ZeroMemClass.zero_def, domain, extendIdealTo_is_extension, extensionOfMax, idealTo, map_zero, toLinearPMap, toLinearPMap.domain, toLinearPMap.map_zero, zero_def, zero_mem
-/
theorem ExtensionOfMaxAdjoin.extendIdealTo_wd' (h : Module.Baer R Q) {y : N} (r : R)
    (eq1 : r • y = 0) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r = 0 := by
  have : r in ideal i f y := by
    change (r • y) in (extensionOfMax i f).toLinearPMap.domain
    rw [eq1]
    apply Submodule.zero_mem _
  rw [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h y r this]
  dsimp [ExtensionOfMaxAdjoin.idealTo]
  simp only [eq1, ← ZeroMemClass.zero_def, (extensionOfMax i f).toLinearPMap.map_zero]

/--
theorem `ExtensionOfMaxAdjoin.extendIdealTo_wd` / 定理 `ExtensionOfMaxAdjoin.extendIdealTo_wd`

English:
theorem ExtensionOfMaxAdjoin.extendIdealTo_wd
  statement: (h : Module.Baer R Q) {y : N} (r r' : R)
  proof: by
  rw [← sub_eq_zero]; rw [← map_sub]
  convert! ExtensionOfMaxAdjoin.extendIdealTo_wd' i f h (r - r') _
  rw [sub_smul]; rw [sub_eq_zero]; rw [eq1]

中文:
定理 ExtensionOfMaxAdjoin.extendIdealTo_wd
  结论: (h : Module.Baer R Q) {y : N} (r r' : R)
  证明: by
  rw [← sub_eq_zero]; rw [← map_sub]
  convert! ExtensionOfMaxAdjoin.extendIdealTo_wd' i f h (r - r') _
  rw [sub_smul]; rw [sub_eq_zero]; rw [eq1]

Depends on / 依赖: ExtensionOfMaxAdjoin, ExtensionOfMaxAdjoin.extendIdealTo_wd, convert, extendIdealTo_wd, map_sub, sub_eq_zero, sub_smul
-/
theorem ExtensionOfMaxAdjoin.extendIdealTo_wd (h : Module.Baer R Q) {y : N} (r r' : R)
    (eq1 : r • y = r' • y) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    ExtensionOfMaxAdjoin.extendIdealTo i f h y r' := by
  rw [← sub_eq_zero]; rw [← map_sub]
  convert! ExtensionOfMaxAdjoin.extendIdealTo_wd' i f h (r - r') _
  rw [sub_smul]; rw [sub_eq_zero]; rw [eq1]

/--
theorem `ExtensionOfMaxAdjoin.extendIdealTo_eq` / 定理 `ExtensionOfMaxAdjoin.extendIdealTo_eq`

English:
theorem ExtensionOfMaxAdjoin.extendIdealTo_eq
  statement: (h : Module.Baer R Q) {y : N} (r : R)
  proof: by
  simp only [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h _ _ hr,
    ExtensionOfMaxAdjoin.idealTo, LinearMap.coe_mk, AddHom.coe_mk]

中文:
定理 ExtensionOfMaxAdjoin.extendIdealTo_eq
  结论: (h : Module.Baer R Q) {y : N} (r : R)
  证明: by
  simp only [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h _ _ hr,
    ExtensionOfMaxAdjoin.idealTo, LinearMap.coe_mk, AddHom.coe_mk]

Depends on / 依赖: AddHom, AddHom.coe_mk, ExtensionOfMaxAdjoin, ExtensionOfMaxAdjoin.extendIdealTo_is_extension, ExtensionOfMaxAdjoin.idealTo, LinearMap, LinearMap.coe_mk, coe_mk, extendIdealTo_is_extension, idealTo
-/
theorem ExtensionOfMaxAdjoin.extendIdealTo_eq (h : Module.Baer R Q) {y : N} (r : R)
    (hr : r • y in (extensionOfMax i f).domain) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    (extensionOfMax i f).toLinearPMap ⟨r • y, hr⟩ := by
  simp only [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h _ _ hr,
    ExtensionOfMaxAdjoin.idealTo, LinearMap.coe_mk, AddHom.coe_mk]

/--
Definition of `ExtensionOfMaxAdjoin.extensionToFun` / `ExtensionOfMaxAdjoin.extensionToFun` 的定义

English:
definition ExtensionOfMaxAdjoin.extensionToFun
  signature: (h : Module.Baer R Q) {y : N}
  body: fun x =>
  (extensionOfMax i f).toLinearPMap (ExtensionOfMaxAdjoin.fst i x) +
    ExtensionOfMaxAdjoin.extendIdealTo i f h y (ExtensionOfMaxAdjoin.snd i x)

中文:
定义 ExtensionOfMaxAdjoin.extensionToFun
  签名: (h : Module.Baer R Q) {y : N}
  定义体: fun x =>
  (extensionOfMax i f).toLinearPMap (ExtensionOfMaxAdjoin.fst i x) +
    ExtensionOfMaxAdjoin.extendIdealTo i f h y (ExtensionOfMaxAdjoin.snd i x)
-/
def ExtensionOfMaxAdjoin.extensionToFun (h : Module.Baer R Q) {y : N} :
    supExtensionOfMaxSingleton i f y -> Q := fun x =>
  (extensionOfMax i f).toLinearPMap (ExtensionOfMaxAdjoin.fst i x) +
    ExtensionOfMaxAdjoin.extendIdealTo i f h y (ExtensionOfMaxAdjoin.snd i x)

/--
theorem `ExtensionOfMaxAdjoin.extensionToFun_wd` / 定理 `ExtensionOfMaxAdjoin.extensionToFun_wd`

English:
theorem ExtensionOfMaxAdjoin.extensionToFun_wd
  statement: (h : Module.Baer R Q) {y : N}
  proof: by
  obtain ⟨a, ha⟩ := a
  have eq2 :
    (ExtensionOfMaxAdjoin.fst i x - a : N) = (r - ExtensionOfMaxAdjoin.snd i x) • y := by
    change x = a + r • y at eq1
    rwa [ExtensionOfMaxAdjoin.eqn, ← sub_eq_zero, ← sub_sub_sub_eq, sub_eq_zero, ← sub_smul]
      at eq1
  have eq3 :=
    ExtensionOfMaxAd

中文:
定理 ExtensionOfMaxAdjoin.extensionToFun_wd
  结论: (h : Module.Baer R Q) {y : N}
  证明: by
  obtain ⟨a, ha⟩ := a
  have eq2 :
    (ExtensionOfMaxAdjoin.fst i x - a : N) = (r - ExtensionOfMaxAdjoin.snd i x) • y := by
    change x = a + r • y at eq1
    rwa [ExtensionOfMaxAdjoin.eqn, ← sub_eq_zero, ← sub_sub_sub_eq, sub_eq_zero, ← sub_smul]
      at eq1
  have eq3 :=
    ExtensionOfMaxAd

Depends on / 依赖: ExtensionOfMaxAdjoin, ExtensionOfMaxAdjoin.eqn, ExtensionOfMaxAdjoin.ex, ExtensionOfMaxAdjoin.extendIdealTo_eq, ExtensionOfMaxAdjoin.fst, ExtensionOfMaxAdjoin.snd, Submodule, Submodule.sub_mem, extendIdealTo_eq, map_sub, sub_eq_iff_eq_add, sub_eq_zero, sub_mem, sub_smul, sub_sub_sub_eq
-/
theorem ExtensionOfMaxAdjoin.extensionToFun_wd (h : Module.Baer R Q) {y : N}
    (x : supExtensionOfMaxSingleton i f y) (a : (extensionOfMax i f).domain)
    (r : R) (eq1 : ↑x = ↑a + r • y) :
    ExtensionOfMaxAdjoin.extensionToFun i f h x =
      (extensionOfMax i f).toLinearPMap a + ExtensionOfMaxAdjoin.extendIdealTo i f h y r := by
  obtain ⟨a, ha⟩ := a
  have eq2 :
    (ExtensionOfMaxAdjoin.fst i x - a : N) = (r - ExtensionOfMaxAdjoin.snd i x) • y := by
    change x = a + r • y at eq1
    rwa [ExtensionOfMaxAdjoin.eqn, ← sub_eq_zero, ← sub_sub_sub_eq, sub_eq_zero, ← sub_smul]
      at eq1
  have eq3 :=
    ExtensionOfMaxAdjoin.extendIdealTo_eq i f h (r - ExtensionOfMaxAdjoin.snd i x)
      (by rw [← eq2]; exact Submodule.sub_mem _ (ExtensionOfMaxAdjoin.fst i x).2 ha)
  simp only [map_sub, sub_smul, sub_eq_iff_eq_add] at eq3
  unfold ExtensionOfMaxAdjoin.extensionToFun
  rw [eq3]; rw [← add_assoc]; rw [← (extensionOfMax i f).toLinearPMap.map_add]; rw [AddMemClass.mk_add_mk]
  congr
  ext
  dsimp
  rw [Subtype.coe_mk]; rw [add_sub]; rw [← eq1]
  exact eq_sub_of_add_eq (ExtensionOfMaxAdjoin.eqn i x).symm

/--
Definition of `extensionOfMaxAdjoin` / `extensionOfMaxAdjoin` 的定义

English:
definition extensionOfMaxAdjoin
  signature: (h : Module.Baer R Q) (y : N)
  body: supExtensionOfMaxSingleton i f y -- (extensionOfMax i f).domain ⊔ Submodule.span R {y}
  le := le_trans (extensionOfMax i f).le le_sup_left
  toFun :=
    { toFun := ExtensionOfMaxAdjoin.extensionToFun i f h
      map_add' := fun a b => by
        have eq1 :
          ↑a + ↑b =
            ↑(Extensi

中文:
定义 extensionOfMaxAdjoin
  签名: (h : Module.Baer R Q) (y : N)
  定义体: supExtensionOfMaxSingleton i f y -- (extensionOfMax i f).domain ⊔ Submodule.span R {y}
  le := le_trans (extensionOfMax i f).le le_sup_left
  toFun :=
    { toFun := ExtensionOfMaxAdjoin.extensionToFun i f h
      map_add' := fun a b => by
        have eq1 :
          ↑a + ↑b =
            ↑(Extensi

Depends on / 依赖: Submodule, Submodule.span, domain, extensionOfMax, supExtensionOfMaxSingleton
-/
def extensionOfMaxAdjoin (h : Module.Baer R Q) (y : N) : ExtensionOf i f where
  domain := supExtensionOfMaxSingleton i f y -- (extensionOfMax i f).domain ⊔ Submodule.span R {y}
  le := le_trans (extensionOfMax i f).le le_sup_left
  toFun :=
    { toFun := ExtensionOfMaxAdjoin.extensionToFun i f h
      map_add' := fun a b => by
        have eq1 :
          ↑a + ↑b =
            ↑(ExtensionOfMaxAdjoin.fst i a + ExtensionOfMaxAdjoin.fst i b) +
              (ExtensionOfMaxAdjoin.snd i a + ExtensionOfMaxAdjoin.snd i b) • y := by
          rw [ExtensionOfMaxAdjoin.eqn]; rw [ExtensionOfMaxAdjoin.eqn]; rw [add_smul]; rw [Submodule.coe_add]
          ac_rfl
        rw [ExtensionOfMaxAdjoin.extensionToFun_wd (y := y) i f h (a + b) _ _ eq1]; rw [LinearPMap.map_add]; rw [map_add]
        unfold ExtensionOfMaxAdjoin.extensionToFun
        abel
      map_smul' := fun r a => by
        dsimp
        have eq1 :
          r • (a : N) =
            ↑(r • ExtensionOfMaxAdjoin.fst i a) + (r • ExtensionOfMaxAdjoin.snd i a) • y := by
          rw [ExtensionOfMaxAdjoin.eqn]; rw [smul_add]; rw [smul_eq_mul]; rw [mul_smul]
          rfl
        rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h (r • a :) _ _ eq1]; rw [map_smul]; rw [LinearPMap.map_smul]; rw [← smul_add]
        congr }
  is_extension m := by
    dsimp
    rw [(extensionOfMax i f).is_extension]; rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h _ ⟨i m]; rw [_⟩ 0 _]; rw [map_zero]; rw [add_zero]
    simp

/--
theorem `extensionOfMax_le` / 定理 `extensionOfMax_le`

English:
theorem extensionOfMax_le
  given: (h : Module.Baer R Q) {y : N}
  proof: ⟨le_sup_left, fun x x' EQ => by
    symm
    change ExtensionOfMaxAdjoin.extensionToFun i f h _ = _
    rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h x' x 0 (by simp [EQ]), map_zero,
      add_zero]⟩

中文:
定理 extensionOfMax_le
  条件: (h : Module.Baer R Q) {y : N}
  证明: ⟨le_sup_left, fun x x' EQ => by
    symm
    change ExtensionOfMaxAdjoin.extensionToFun i f h _ = _
    rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h x' x 0 (by simp [EQ]), map_zero,
      add_zero]⟩

Depends on / 依赖: ExtensionOfMaxAdjoin, ExtensionOfMaxAdjoin.extensionToFun, ExtensionOfMaxAdjoin.extensionToFun_wd, add_zero, extensionToFun, extensionToFun_wd, le_sup_left, map_zero
-/
theorem extensionOfMax_le (h : Module.Baer R Q) {y : N} :
    extensionOfMax i f <= extensionOfMaxAdjoin i f h y :=
  ⟨le_sup_left, fun x x' EQ => by
    symm
    change ExtensionOfMaxAdjoin.extensionToFun i f h _ = _
    rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h x' x 0 (by simp [EQ]), map_zero,
      add_zero]⟩

/--
theorem `extensionOfMax_to_submodule_eq_top` / 定理 `extensionOfMax_to_submodule_eq_top`

English:
theorem extensionOfMax_to_submodule_eq_top
  given: (h : Module.Baer R Q)
  proof: by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [← extensionOfMax_is_max i f _ (extensionOfMax_le i f h)]; rw [extensionOfMaxAdjoin]; rw [Submodule.mem_sup]
  exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, zero_add _⟩

中文:
定理 extensionOfMax_to_submodule_eq_top
  条件: (h : Module.Baer R Q)
  证明: by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [← extensionOfMax_is_max i f _ (extensionOfMax_le i f h)]; rw [extensionOfMaxAdjoin]; rw [Submodule.mem_sup]
  exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, zero_add _⟩

Depends on / 依赖: Submodule, Submodule.eq_top_iff, Submodule.mem_span_singleton_self, Submodule.mem_sup, Submodule.zero_mem, eq_top_iff, extensionOfMaxAdjoin, extensionOfMax_is_max, extensionOfMax_le, mem_span_singleton_self, mem_sup, zero_add, zero_mem
-/
theorem extensionOfMax_to_submodule_eq_top (h : Module.Baer R Q) :
    (extensionOfMax i f).domain = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [← extensionOfMax_is_max i f _ (extensionOfMax_le i f h)]; rw [extensionOfMaxAdjoin]; rw [Submodule.mem_sup]
  exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, zero_add _⟩

/--
theorem `extension_property` / 定理 `extension_property`

English:
theorem extension_property
  statement: (h : Module.Baer R Q)
  proof: haveI : Fact (Function.Injective f) := ⟨hf⟩
  Exists.intro
    { toFun := ((extensionOfMax f g).toLinearPMap
        ⟨·, (extensionOfMax_to_submodule_eq_top f g h).symm ▸ ⟨⟩⟩)
      map_add' := fun x y => by rw [← LinearPMap.map_add]; congr
      map_smul' := fun r x => by rw [← LinearPMap.map_smul]

中文:
定理 extension_property
  结论: (h : Module.Baer R Q)
  证明: haveI : Fact (Function.Injective f) := ⟨hf⟩
  Exists.intro
    { toFun := ((extensionOfMax f g).toLinearPMap
        ⟨·, (extensionOfMax_to_submodule_eq_top f g h).symm ▸ ⟨⟩⟩)
      map_add' := fun x y => by rw [← LinearPMap.map_add]; congr
      map_smul' := fun r x => by rw [← LinearPMap.map_smul]
-/
protected theorem extension_property (h : Module.Baer R Q)
    (f : M ->ₗ[R] N) (hf : Function.Injective f) (g : M ->ₗ[R] Q) : exists h, h ∘ₗ f = g :=
  haveI : Fact (Function.Injective f) := ⟨hf⟩
  Exists.intro
    { toFun := ((extensionOfMax f g).toLinearPMap
        ⟨·, (extensionOfMax_to_submodule_eq_top f g h).symm ▸ ⟨⟩⟩)
      map_add' := fun x y => by rw [← LinearPMap.map_add]; congr
      map_smul' := fun r x => by rw [← LinearPMap.map_smul]; dsimp } <|
    LinearMap.ext fun x => ((extensionOfMax f g).is_extension x).symm

/--
theorem `extension_property_addMonoidHom` / 定理 `extension_property_addMonoidHom`

English:
theorem extension_property_addMonoidHom
  statement: (h : Module.Baer Int Q)
  proof: have ⟨g', hg'⟩ := h.extension_property f.toIntLinearMap hf g.toIntLinearMap
  ⟨g', congr(LinearMap.toAddMonoidHom $hg')⟩

中文:
定理 extension_property_addMonoidHom
  结论: (h : Module.Baer 整数 Q)
  证明: have ⟨g', hg'⟩ := h.extension_property f.toIntLinearMap hf g.toIntLinearMap
  ⟨g', congr(LinearMap.toAddMonoidHom $hg')⟩

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom, extension_property, f.toIntLinearMap, g.toIntLinearMap, h.extension_property, toAddMonoidHom, toIntLinearMap
-/
theorem extension_property_addMonoidHom (h : Module.Baer Int Q)
    (f : M ->+ N) (hf : Function.Injective f) (g : M ->+ Q) : exists h : N ->+ Q, h.comp f = g :=
  have ⟨g', hg'⟩ := h.extension_property f.toIntLinearMap hf g.toIntLinearMap
  ⟨g', congr(LinearMap.toAddMonoidHom $hg')⟩

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (h : Module.Baer R Q)
  statement: Module.Injective R Q where
  proof: by
    obtain ⟨h, H⟩ := Module.Baer.extension_property h i hi f
    exact ⟨h, DFunLike.congr_fun H⟩

中文:
定理 injective
  条件: (h : Module.Baer R Q)
  结论: Module.Injective R Q where
  证明: by
    obtain ⟨h, H⟩ := Module.Baer.extension_property h i hi f
    exact ⟨h, DFunLike.congr_fun H⟩
-/
protected theorem injective (h : Module.Baer R Q) : Module.Injective R Q where
  out X Y _ _ _ _ i hi f := by
    obtain ⟨h, H⟩ := Module.Baer.extension_property h i hi f
    exact ⟨h, DFunLike.congr_fun H⟩

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: [Small.{v} R] (inj : Module.Injective R Q)
  statement: Module.Baer R Q
  proof: by
  intro I g
  let eI := Shrink.linearEquiv R I
  let eR := Shrink.linearEquiv R R
  obtain ⟨g', hg'⟩ := Module.Injective.out (eR.symm.toLinearMap ∘ₗ I.subtype ∘ₗ eI.toLinearMap)
    (eR.symm.injective.comp <| Subtype.val_injective.comp eI.injective) (g ∘ₗ eI.toLinearMap)
  exact ⟨g' ∘ₗ eR.symm.to

中文:
定理 of_injective
  条件: [Small.{v} R] (inj : Module.Injective R Q)
  结论: Module.Baer R Q
  证明: by
  intro I g
  let eI := Shrink.linearEquiv R I
  let eR := Shrink.linearEquiv R R
  obtain ⟨g', hg'⟩ := Module.Injective.out (eR.symm.toLinearMap ∘ₗ I.subtype ∘ₗ eI.toLinearMap)
    (eR.symm.injective.comp <| Subtype.val_injective.comp eI.injective) (g ∘ₗ eI.toLinearMap)
  exact ⟨g' ∘ₗ eR.symm.to

Depends on / 依赖: DivisionSemiring, DivisionSemiring.to_moduleIsTorsionFree, IsTorsionFree, to_moduleIsTorsionFree
-/
protected theorem of_injective [Small.{v} R] (inj : Module.Injective R Q) : Module.Baer R Q := by
  intro I g
  let eI := Shrink.linearEquiv R I
  let eR := Shrink.linearEquiv R R
  obtain ⟨g', hg'⟩ := Module.Injective.out (eR.symm.toLinearMap ∘ₗ I.subtype ∘ₗ eI.toLinearMap)
    (eR.symm.injective.comp <| Subtype.val_injective.comp eI.injective) (g ∘ₗ eI.toLinearMap)
  exact ⟨g' ∘ₗ eR.symm.toLinearMap, fun x mx => by simpa [eI, eR] using hg' (equivShrink I ⟨x, mx⟩)⟩

/--
theorem `iff_injective` / 定理 `iff_injective`

English:
theorem iff_injective
  given: [Small.{v} R]
  statement: Module.Baer R Q ↔ Module.Injective R Q
  proof: ⟨Module.Baer.injective, Module.Baer.of_injective⟩

中文:
定理 iff_injective
  条件: [Small.{v} R]
  结论: Module.Baer R Q ↔ Module.Injective R Q
  证明: ⟨Module.Baer.injective, Module.Baer.of_injective⟩
-/
protected theorem iff_injective [Small.{v} R] : Module.Baer R Q ↔ Module.Injective R Q :=
  ⟨Module.Baer.injective, Module.Baer.of_injective⟩

end Module.Baer

section ULift

variable {M : Type v} [AddCommGroup M] [Module R M]

/--
lemma `Module.ulift_injective_of_injective` / 引理 `Module.ulift_injective_of_injective`

English:
lemma Module.ulift_injective_of_injective
  statement: [Small.{v} R]
  proof: Module.Baer.injective fun I g =>
  have ⟨g', hg'⟩ := Module.Baer.iff_injective.mpr inj I (ULift.moduleEquiv.toLinearMap ∘ₗ g)
⟨ULift.moduleEquiv.symm.toLinearMap ∘ₗ g', fun r hr => ULift.ext _ _ hg' r hr⟩

中文:
引理 Module.ulift_injective_of_injective
  结论: [Small.{v} R]
  证明: Module.Baer.injective fun I g =>
  have ⟨g', hg'⟩ := Module.Baer.iff_injective.mpr inj I (ULift.moduleEquiv.toLinearMap ∘ₗ g)
⟨ULift.moduleEquiv.symm.toLinearMap ∘ₗ g', fun r hr => ULift.ext _ _ hg' r hr⟩

Depends on / 依赖: Module, Module.Baer.injective, injective
-/
lemma Module.ulift_injective_of_injective [Small.{v} R]
    (inj : Module.Injective R M) :
    Module.Injective R (ULift.{v'} M) := Module.Baer.injective fun I g =>
  have ⟨g', hg'⟩ := Module.Baer.iff_injective.mpr inj I (ULift.moduleEquiv.toLinearMap ∘ₗ g)
⟨ULift.moduleEquiv.symm.toLinearMap ∘ₗ g', fun r hr => ULift.ext _ _ hg' r hr⟩

/--
lemma `Module.injective_of_ulift_injective` / 引理 `Module.injective_of_ulift_injective`

English:
lemma Module.injective_of_ulift_injective
  proof: let eX := ULift.moduleEquiv.{_, _, v'} (R := R) (M := X)
    have ⟨g', hg'⟩ := inj.out (ULift.moduleEquiv.{_, _, v'}.symm.toLinearMap ∘ₗ f ∘ₗ eX.toLinearMap)
      (by exact ULift.moduleEquiv.symm.injective.comp <| hf.comp eX.injective)
      (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ eX.toLinearMa

中文:
引理 Module.injective_of_ulift_injective
  证明: let eX := ULift.moduleEquiv.{_, _, v'} (R := R) (M := X)
    have ⟨g', hg'⟩ := inj.out (ULift.moduleEquiv.{_, _, v'}.symm.toLinearMap ∘ₗ f ∘ₗ eX.toLinearMap)
      (by exact ULift.moduleEquiv.symm.injective.comp <| hf.comp eX.injective)
      (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ eX.toLinearMa

Depends on / 依赖: ULift.down, ULift.moduleEquiv, ULift.moduleEquiv.symm.injective.comp, ULift.moduleEquiv.symm.toLinearMap, ULift.moduleEquiv.toLinearMap, eX.injective, eX.toLinearMap, hf.comp, inj.out, injective, moduleEquiv, symm.toLinearMap, toLinearMap
-/
lemma Module.injective_of_ulift_injective
    (inj : Module.Injective R (ULift.{v'} M)) :
    Module.Injective R M where
  out X Y _ _ _ _ f hf g :=
    let eX := ULift.moduleEquiv.{_, _, v'} (R := R) (M := X)
    have ⟨g', hg'⟩ := inj.out (ULift.moduleEquiv.{_, _, v'}.symm.toLinearMap ∘ₗ f ∘ₗ eX.toLinearMap)
      (by exact ULift.moduleEquiv.symm.injective.comp <| hf.comp eX.injective)
      (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ eX.toLinearMap)
    ⟨ULift.moduleEquiv.toLinearMap ∘ₗ g' ∘ₗ ULift.moduleEquiv.symm.toLinearMap,
      fun x => by exact congr(ULift.down $(hg' ⟨x⟩))⟩

variable (M) [Small.{v} R]

/--
lemma `Module.injective_iff_ulift_injective` / 引理 `Module.injective_iff_ulift_injective`

English:
lemma Module.injective_iff_ulift_injective
  proof: ⟨Module.ulift_injective_of_injective R,
   Module.injective_of_ulift_injective R⟩

中文:
引理 Module.injective_iff_ulift_injective
  证明: ⟨Module.ulift_injective_of_injective R,
   Module.injective_of_ulift_injective R⟩

Depends on / 依赖: Module, Module.injective_of_ulift_injective, Module.ulift_injective_of_injective, injective_of_ulift_injective, ulift_injective_of_injective
-/
lemma Module.injective_iff_ulift_injective :
    Module.Injective R M ↔ Module.Injective R (ULift.{v'} M) :=
  ⟨Module.ulift_injective_of_injective R,
   Module.injective_of_ulift_injective R⟩

end ULift

section lifting_property

universe uR uM uP uP'

variable (R : Type uR) [Ring R] [Small.{uM} R]
variable (M : Type uM) [AddCommGroup M] [Module R M] [inj : Module.Injective R M]
variable (P : Type uP) [AddCommGroup P] [Module R P]
variable (P' : Type uP') [AddCommGroup P'] [Module R P']

/--
lemma `Module.Injective.extension_property` / 引理 `Module.Injective.extension_property`

English:
lemma Module.Injective.extension_property
  proof: (Module.Baer.of_injective inj).extension_property f hf g

中文:
引理 Module.Injective.extension_property
  证明: (Module.Baer.of_injective inj).extension_property f hf g

Depends on / 依赖: Module, Module.Baer.of_injective, extension_property, of_injective
-/
lemma Module.Injective.extension_property
    (f : P ->ₗ[R] P') (hf : Function.Injective f)
    (g : P ->ₗ[R] M) : exists h : P' ->ₗ[R] M, h ∘ₗ f = g :=
  (Module.Baer.of_injective inj).extension_property f hf g

end lifting_property


universe w in
/--
Instance `Module.Injective.pi` / 实例 `Module.Injective.pi`

English:
instance Module.Injective.pi
  body: ⟨fun X Y _ _ _ _ f hf g => by
    choose l hl using fun i => extension_property R _ _ _ f hf ((LinearMap.proj i).comp g)
    refine ⟨LinearMap.pi l, fun x => ?_⟩
    ext i
    exact DFunLike.congr_fun (hl i) x⟩

中文:
实例 Module.Injective.pi
  定义体: ⟨fun X Y _ _ _ _ f hf g => by
    choose l hl using fun i => extension_property R _ _ _ f hf ((LinearMap.proj i).comp g)
    refine ⟨LinearMap.pi l, fun x => ?_⟩
    ext i
    exact DFunLike.congr_fun (hl i) x⟩

Depends on / 依赖: DFunLike, DFunLike.congr_fun, LinearMap, LinearMap.pi, LinearMap.proj, congr_fun, extension_property
-/
instance Module.Injective.pi
    (R : Type u) [Ring R] {ι : Type w} (M : ι -> Type v) [Small.{v} R]
    [forall i, AddCommGroup (M i)] [forall i, Module R (M i)]
    [forall i, Module.Injective R (M i)] :
    Module.Injective R (forall i, M i) :=
  ⟨fun X Y _ _ _ _ f hf g => by
    choose l hl using fun i => extension_property R _ _ _ f hf ((LinearMap.proj i).comp g)
    refine ⟨LinearMap.pi l, fun x => ?_⟩
    ext i
    exact DFunLike.congr_fun (hl i) x⟩

set_option backward.isDefEq.respectTransparency false in
universe u' in
attribute [local instance] RingHomInvPair.of_ringEquiv in
/--
theorem `Module.Injective.of_ringEquiv` / 定理 `Module.Injective.of_ringEquiv`

English:
theorem Module.Injective.of_ringEquiv
  statement: {R : Type u} [Ring R] [Small.{v} R] {S : Type u'} [Ring S]
  proof: by
  apply Module.Baer.injective (fun I g => ?_)
  let I' := Submodule.map e₁.symm.toSemilinearEquiv.toLinearMap I
  let e : I' ≃ₛₗ[RingHomClass.toRingHom e₁] I := (e₁.symm.toSemilinearEquiv.submoduleMap I).symm
  let f : I' ->ₗ[R] M := e₂.symm.toLinearMap.comp (g.comp e.toLinearMap)
  have hf (x) (

中文:
定理 Module.Injective.of_ringEquiv
  结论: {R : 类型u} [Ring R] [Small.{v} R] {S : 类型u'} [Ring S]
  证明: by
  apply Module.Baer.injective (fun I g => ?_)
  let I' := Submodule.map e₁.symm.toSemilinearEquiv.toLinearMap I
  let e : I' ≃ₛₗ[RingHomClass.toRingHom e₁] I := (e₁.symm.toSemilinearEquiv.submoduleMap I).symm
  let f : I' ->ₗ[R] M := e₂.symm.toLinearMap.comp (g.comp e.toLinearMap)
  have hf (x) (

Depends on / 依赖: Module, Module.Baer.injective, Module.Baer.of_injective, RingHomClass, RingHomClass.toRingHom, Submodule, Submodule.map, e.toLinearMap, g.comp, injective, of_injective, submoduleMap, symm.toLinearMap.comp, symm.toSemilinearEquiv.submoduleMap, symm.toSemilinearEquiv.toLinearMap, toLinearMap, toRingHom, toSemilinearEquiv, toSemilinearEquiv.symm.toLinearMap
-/
theorem Module.Injective.of_ringEquiv {R : Type u} [Ring R] [Small.{v} R] {S : Type u'} [Ring S]
    {M : Type v} {N : Type v'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] N)
    [inj : Module.Injective R M] : Module.Injective S N := by
  apply Module.Baer.injective (fun I g => ?_)
  let I' := Submodule.map e₁.symm.toSemilinearEquiv.toLinearMap I
  let e : I' ≃ₛₗ[RingHomClass.toRingHom e₁] I := (e₁.symm.toSemilinearEquiv.submoduleMap I).symm
  let f : I' ->ₗ[R] M := e₂.symm.toLinearMap.comp (g.comp e.toLinearMap)
  have hf (x) (hx : x in I') : f ⟨x, hx⟩ = e₂.symm (g ⟨e₁ x, by simp_all [I']⟩) := rfl
  obtain ⟨f', hf'⟩ := Module.Baer.of_injective ‹_› I' f
  exact ⟨e₂.toLinearMap ∘ₛₗ f' ∘ₛₗ e₁.toSemilinearEquiv.symm.toLinearMap, by simp_all [I']⟩
