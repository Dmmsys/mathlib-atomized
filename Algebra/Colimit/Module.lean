/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Jujian Zhang
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Congruence.Defs
public import Mathlib.Data.Finset.Order
public import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of modules and abelian groups

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups.

It is constructed as a quotient of the free module instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

## Main definitions

* `Module.DirectLimit G f`
* `AddCommGroup.DirectLimit G f`

-/

@[expose] public section

suppress_compilation
noncomputable section -- needed for `deriving`

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι -> Type*}

open Submodule

namespace Module

alias DirectedSystem.map_self := DirectedSystem.map_self'
alias DirectedSystem.map_map := DirectedSystem.map_map'

variable [forall i, AddCommMonoid (G i)] [forall i, Module R (G i)] (f : forall i j, i <= j -> G i ->ₗ[R] G j)

/--
Inductive type `DirectLimit.Eqv` / 归纳类型 `DirectLimit.Eqv`

English:
inductive DirectLimit.Eqv
  parameters: [DecidableEq ι]
  constructors (1):
    - of_map: {i j} (h : i <= j) (x : G i) : Eqv (DirectSum.lof R ι G i x) (DirectSum.lof R ι G j <| f i j h x)

中文:
归纳类型 DirectLimit.Eqv
  参数: [DecidableEq ι]
  构造子 (1 个):
    - of_map: {i j} (h : i <= j) (x : G i) : Eqv (DirectSum.lof R ι G i x) (DirectSum.lof R ι G j <| f i j h x)
-/
inductive DirectLimit.Eqv [DecidableEq ι] : DirectSum ι G -> DirectSum ι G -> Prop
  | of_map {i j} (h : i <= j) (x : G i) :
    Eqv (DirectSum.lof R ι G i x) (DirectSum.lof R ι G j <| f i j h x)

/--
Definition of `DirectLimit.moduleCon` / `DirectLimit.moduleCon` 的定义

English:
definition DirectLimit.moduleCon
  signature: [DecidableEq ι]
  body: SMulCon.addConGen' (Eqv f) by rintro _ _ _ ⟨⟩; simpa only [← map_smul] using .of_map ..

中文:
定义 DirectLimit.moduleCon
  签名: [DecidableEq ι]
  定义体: SMulCon.addConGen' (Eqv f) by rintro _ _ _ ⟨⟩; simpa only [← map_smul] using .of_map ..

Depends on / 依赖: SMulCon, SMulCon.addConGen, addConGen, map_smul, of_map
-/
def DirectLimit.moduleCon [DecidableEq ι] : ModuleCon R (DirectSum ι G) :=
SMulCon.addConGen' (Eqv f) by rintro _ _ _ ⟨⟩; simpa only [← map_smul] using .of_map ..

variable (G)

/--
Definition of `DirectLimit` / `DirectLimit` 的定义

English:
definition DirectLimit
  signature: [DecidableEq ι]
  body: (DirectLimit.moduleCon f).Quotient

中文:
定义 DirectLimit
  签名: [DecidableEq ι]
  定义体: (DirectLimit.moduleCon f).Quotient

Depends on / 依赖: DirectLimit, DirectLimit.moduleCon, Quotient, moduleCon
-/
def DirectLimit [DecidableEq ι] : Type _ := (DirectLimit.moduleCon f).Quotient

variable [DecidableEq ι]

namespace DirectLimit

section Basic

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (DirectLimit G f)
  body: inferInstanceAs (AddCommMonoid (moduleCon f).Quotient)

中文:
实例 addCommMonoid
  签名: : AddCommMonoid (DirectLimit G f)
  定义体: inferInstanceAs (AddCommMonoid (moduleCon f).Quotient)

Depends on / 依赖: AddCommMonoid, Quotient, moduleCon
-/
instance addCommMonoid : AddCommMonoid (DirectLimit G f) :=
  inferInstanceAs (AddCommMonoid (moduleCon f).Quotient)

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: : Module R (DirectLimit G f)
  body: inferInstanceAs (Module R (moduleCon f).Quotient)

中文:
实例 module
  签名: : Module R (DirectLimit G f)
  定义体: inferInstanceAs (Module R (moduleCon f).Quotient)

Depends on / 依赖: Module, Quotient, moduleCon
-/
instance module : Module R (DirectLimit G f) := inferInstanceAs (Module R (moduleCon f).Quotient)

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: (G : ι -> Type*) [forall i, AddCommGroup (G i)] [forall i, Module R (G i)]
  body: inferInstanceAs (AddCommGroup (moduleCon f).Quotient)

中文:
实例 addCommGroup
  签名: (G : ι -> 类型) [对任意 i, AddCommGroup (G i)] [对任意 i, Module R (G i)]
  定义体: inferInstanceAs (AddCommGroup (moduleCon f).Quotient)

Depends on / 依赖: AddCommGroup, Quotient, moduleCon
-/
instance addCommGroup (G : ι -> Type*) [forall i, AddCommGroup (G i)] [forall i, Module R (G i)]
    (f : forall i j, i <= j -> G i ->ₗ[R] G j) : AddCommGroup (DirectLimit G f) :=
  inferInstanceAs (AddCommGroup (moduleCon f).Quotient)

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (DirectLimit G f)
  body: ⟨0⟩

中文:
实例 inhabited
  签名: : Inhabited (DirectLimit G f)
  定义体: ⟨0⟩
-/
instance inhabited : Inhabited (DirectLimit G f) :=
  ⟨0⟩

/--
Instance `unique` / 实例 `unique`

English:
instance unique
  signature: [IsEmpty ι]
  body: inferInstanceAs Unique (Quotient _)

中文:
实例 unique
  签名: [IsEmpty ι]
  定义体: inferInstanceAs Unique (Quotient _)

Depends on / 依赖: Quotient, Unique
-/
instance unique [IsEmpty ι] : Unique (DirectLimit G f) :=
inferInstanceAs Unique (Quotient _)

variable (R ι)

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (i)
  body: .comp { __ := AddCon.mk' _, map_smul' := fun _ _ => rfl } DirectSum.lof R ι G i

中文:
定义 of
  签名: (i)
  定义体: .comp { __ := AddCon.mk' _, map_smul' := fun _ _ => rfl } DirectSum.lof R ι G i

Depends on / 依赖: AddCon, AddCon.mk, DirectSum, DirectSum.lof, map_smul
-/
def of (i) : G i ->ₗ[R] DirectLimit G f :=
.comp { __ := AddCon.mk' _, map_smul' := fun _ _ => rfl } DirectSum.lof R ι G i

variable {R ι G f}

/--
theorem `quotMk_of` / 定理 `quotMk_of`

English:
theorem quotMk_of
  given: (i x)
  statement: Quot.mk _ (.of G i x) = of R ι G f i x
  proof: rfl

@[simp]

中文:
定理 quotMk_of
  条件: (i x)
  结论: Quot.mk _ (.of G i x) = of R ι G f i x
  证明: rfl

@[simp]
-/
theorem quotMk_of (i x) : Quot.mk _ (.of G i x) = of R ι G f i x := rfl

@[simp]
/--
theorem `of_f` / 定理 `of_f`

English:
theorem of_f
  given: {i j hij x}
  statement: of R ι G f j (f i j hij x) = of R ι G f i x
  proof: (AddCon.eq _).mpr .symm .of _ _ (.of_map _ _)

中文:
定理 of_f
  条件: {i j hij x}
  结论: of R ι G f j (f i j hij x) = of R ι G f i x
  证明: (AddCon.eq _).mpr .symm .of _ _ (.of_map _ _)

Depends on / 依赖: AddCon, AddCon.eq, of_map
-/
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x :=
(AddCon.eq _).mpr .symm .of _ _ (.of_map _ _)

/--
theorem `exists_of` / 定理 `exists_of`

English:
theorem exists_of
  given: [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f)
  proof: Nonempty.elim (by infer_instance) fun ind : ι =>
    Quotient.inductionOn' z fun z =>
      DirectSum.induction_on z ⟨ind, 0, map_zero _⟩ (fun i x => ⟨i, x, rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ =>
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by
      

中文:
定理 exists_of
  条件: [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f)
  证明: Nonempty.elim (by infer_instance) fun ind : ι =>
    Quotient.inductionOn' z fun z =>
      DirectSum.induction_on z ⟨ind, 0, map_zero _⟩ (fun i x => ⟨i, x, rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ =>
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by
      

Depends on / 依赖: DirectSum, DirectSum.induction_on, Nonempty, Nonempty.elim, Quotient, Quotient.inductionOn, exists_ge_ge, inductionOn, induction_on, infer_instance, map_add, map_zero, of_f
-/
theorem exists_of [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f) :
    exists i x, of R ι G f i x = z :=
  Nonempty.elim (by infer_instance) fun ind : ι =>
    Quotient.inductionOn' z fun z =>
      DirectSum.induction_on z ⟨ind, 0, map_zero _⟩ (fun i x => ⟨i, x, rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ =>
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by
          rw [map_add]; rw [of_f]; rw [of_f]; rw [ihx]; rw [ihy]
          rfl ⟩

/--
theorem `exists_of₂` / 定理 `exists_of₂`

English:
theorem exists_of₂
  given: [Nonempty ι] [IsDirectedOrder ι] (z w : DirectLimit G f)
  proof: have ⟨i, x, hx⟩ := exists_of z
  have ⟨j, y, hy⟩ := exists_of w
  have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  ⟨k, f i k hik x, f j k hjk y, by rw [of_f, hx], by rw [of_f, hy]⟩

@[elab_as_elim]

中文:
定理 exists_of₂
  条件: [Nonempty ι] [IsDirectedOrder ι] (z w : DirectLimit G f)
  证明: have ⟨i, x, hx⟩ := exists_of z
  have ⟨j, y, hy⟩ := exists_of w
  have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  ⟨k, f i k hik x, f j k hjk y, by rw [of_f, hx], by rw [of_f, hy]⟩

@[elab_as_elim]

Depends on / 依赖: exists_ge_ge, exists_of, of_f
-/
theorem exists_of₂ [Nonempty ι] [IsDirectedOrder ι] (z w : DirectLimit G f) :
    exists i x y, of R ι G f i x = z ∧ of R ι G f i y = w :=
  have ⟨i, x, hx⟩ := exists_of z
  have ⟨j, y, hy⟩ := exists_of w
  have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  ⟨k, f i k hik x, f j k hjk y, by rw [of_f, hx], by rw [of_f, hy]⟩

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f -> Prop}
  proof: let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x

中文:
定理 induction_on
  结论: [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f -> 命题}
  证明: let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x
-/
protected theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f -> Prop}
    (z : DirectLimit G f) (ih : forall i x, C (of R ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (R ι G f) in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (g : forall i, G i ->ₗ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)
  body: AddCon.lift _ (DirectSum.toModule R ι P g)
    AddCon.addConGen_le.2 fun _ _ ⟨_, _⟩ => by simpa using (Hg _ _ _ _).symm
  map_smul' r := by rintro ⟨x⟩; exact map_smul (DirectSum.toModule R ι P g) r x

中文:
定义 lift
  签名: (g : 对任意 i, G i ->ₗ[R] P) (Hg : 对任意 i j hij x, g j (f i j hij x) = g i x)
  定义体: AddCon.lift _ (DirectSum.toModule R ι P g)
    AddCon.addConGen_le.2 fun _ _ ⟨_, _⟩ => by simpa using (Hg _ _ _ _).symm
  map_smul' r := by rintro ⟨x⟩; exact map_smul (DirectSum.toModule R ι P g) r x

Depends on / 依赖: AddCon, AddCon.lift, DirectSum, DirectSum.toModule, toModule
-/
def lift (g : forall i, G i ->ₗ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ->ₗ[R] P where
__ := AddCon.lift _ (DirectSum.toModule R ι P g)
    AddCon.addConGen_le.2 fun _ _ ⟨_, _⟩ => by simpa using (Hg _ _ _ _).symm
  map_smul' r := by rintro ⟨x⟩; exact map_smul (DirectSum.toModule R ι P g) r x

variable (g : forall i, G i ->ₗ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: {i} (x)
  statement: lift R ι G f g Hg (of R ι G f i x) = g i x
  proof: DirectSum.toModule_lof R _ _

@[ext]

中文:
定理 lift_of
  条件: {i} (x)
  结论: lift R ι G f g Hg (of R ι G f i x) = g i x
  证明: DirectSum.toModule_lof R _ _

@[ext]
-/
@[simp] theorem lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x :=
  DirectSum.toModule_lof R _ _

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {g₁ g₂ : DirectLimit G f ->ₗ[R] P}
  proof: LinearMap.toAddMonoidHom_injective AddCon.hom_ext DirectSum.addHom_ext' fun i =>
    congr($(h i).toAddMonoidHom)

@[simp]

中文:
定理 hom_ext
  结论: {g₁ g₂ : DirectLimit G f ->ₗ[R] P}
  证明: LinearMap.toAddMonoidHom_injective AddCon.hom_ext DirectSum.addHom_ext' fun i =>
    congr($(h i).toAddMonoidHom)

@[simp]

Depends on / 依赖: AddCon, AddCon.hom_ext, DirectSum, DirectSum.addHom_ext, LinearMap, LinearMap.toAddMonoidHom_injective, addHom_ext, hom_ext, toAddMonoidHom, toAddMonoidHom_injective
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f ->ₗ[R] P}
    (h : forall i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) :
    g₁ = g₂ :=
LinearMap.toAddMonoidHom_injective AddCon.hom_ext DirectSum.addHom_ext' fun i =>
    congr($(h i).toAddMonoidHom)

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: (F : DirectLimit G f ->ₗ[R] P)
  proof: by
  ext; simp

@[simp]

中文:
定理 lift_comp_of
  条件: (F : DirectLimit G f ->ₗ[R] P)
  证明: by
  ext; simp

@[simp]
-/
theorem lift_comp_of (F : DirectLimit G f ->ₗ[R] P) :
    lift R ι G f (fun i => F.comp <| of R ι G f i) (fun i j hij x => by simp) = F := by
  ext; simp

@[simp]
/--
theorem `lift_of'` / 定理 `lift_of'`

English:
theorem lift_of'
  statement: lift R ι G f (of R ι G f) (fun i j hij x => by simp) = .id
  proof: by
  ext; simp

中文:
定理 lift_of'
  结论: lift R ι G f (of R ι G f) (fun i j hij x => by simp) = .id
  证明: by
  ext; simp
-/
theorem lift_of' : lift R ι G f (of R ι G f) (fun i j hij x => by simp) = .id := by
  ext; simp

/--
lemma `lift_injective` / 引理 `lift_injective`

English:
lemma lift_injective
  statement: [IsDirectedOrder ι]
  proof: by
  cases isEmpty_or_nonempty ι
  · apply Function.injective_of_subsingleton
  intro z w eq
  obtain ⟨i, x, y, rfl, rfl⟩ := exists_of₂ z w
  simp_rw [lift_of] at eq
  rw [injective _ eq]

中文:
引理 lift_injective
  结论: [IsDirectedOrder ι]
  证明: by
  cases isEmpty_or_nonempty ι
  · apply Function.injective_of_subsingleton
  intro z w eq
  obtain ⟨i, x, y, rfl, rfl⟩ := exists_of₂ z w
  simp_rw [lift_of] at eq
  rw [injective _ eq]

Depends on / 依赖: Function, Function.injective_of_subsingleton, injective, injective_of_subsingleton, isEmpty_or_nonempty, lift_of, simp_rw
-/
lemma lift_injective [IsDirectedOrder ι]
    (injective : forall i, Function.Injective <| g i) :
    Function.Injective (lift R ι G f g Hg) := by
  cases isEmpty_or_nonempty ι
  · apply Function.injective_of_subsingleton
  intro z w eq
  obtain ⟨i, x, y, rfl, rfl⟩ := exists_of₂ z w
  simp_rw [lift_of] at eq
  rw [injective _ eq]

section functorial

variable {G' : ι -> Type*} [forall i, AddCommMonoid (G' i)] [forall i, Module R (G' i)]
variable {f' : forall i j, i <= j -> G' i ->ₗ[R] G' j}
variable {G'' : ι -> Type*} [forall i, AddCommMonoid (G'' i)] [forall i, Module R (G'' i)]
variable {f'' : forall i j, i <= j -> G'' i ->ₗ[R] G'' j}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (g : (i : ι) -> G i ->ₗ[R] G' i) (hg : forall i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
  body: lift _ _ _ _ (fun i => of _ _ _ _ _ ∘ₗ g i) fun i j h g => by
    have eq1 := LinearMap.congr_fun (hg i j h) g
    simp only [LinearMap.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1]; rw [of_f]

中文:
定义 map
  签名: (g : (i : ι) -> G i ->ₗ[R] G' i) (hg : 对任意 i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
  定义体: lift _ _ _ _ (fun i => of _ _ _ _ _ ∘ₗ g i) fun i j h g => by
    have eq1 := LinearMap.congr_fun (hg i j h) g
    simp only [LinearMap.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1]; rw [of_f]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.congr_fun, coe_comp, comp_apply, congr_fun, of_f
-/
def map (g : (i : ι) -> G i ->ₗ[R] G' i) (hg : forall i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i) :
    DirectLimit G f ->ₗ[R] DirectLimit G' f' :=
  lift _ _ _ _ (fun i => of _ _ _ _ _ ∘ₗ g i) fun i j h g => by
    have eq1 := LinearMap.congr_fun (hg i j h) g
    simp only [LinearMap.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1]; rw [of_f]

/--
lemma `map_apply_of` / 引理 `map_apply_of`

English:
lemma map_apply_of
  statement: (g : (i : ι) -> G i ->ₗ[R] G' i)
  proof: lift_of _ _ _

中文:
引理 map_apply_of
  结论: (g : (i : ι) -> G i ->ₗ[R] G' i)
  证明: lift_of _ _ _
-/
@[simp] lemma map_apply_of (g : (i : ι) -> G i ->ₗ[R] G' i)
    (hg : forall i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    {i : ι} (x : G i) :
    map g hg (of _ _ G f _ x) = of R ι G' f' i (g i x) :=
  lift_of _ _ _

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  proof: by
  ext; simp

中文:
引理 map_id
  证明: by
  ext; simp
-/
@[simp] lemma map_id :
    map (fun _ => LinearMap.id) (fun _ _ _ => rfl) = LinearMap.id (M := DirectLimit G f) := by
  ext; simp

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: (g₁ : (i : ι) -> G i ->ₗ[R] G' i) (g₂ : (i : ι) -> G' i ->ₗ[R] G'' i)
  proof: by
  ext; simp

中文:
引理 map_comp
  结论: (g₁ : (i : ι) -> G i ->ₗ[R] G' i) (g₂ : (i : ι) -> G' i ->ₗ[R] G'' i)
  证明: by
  ext; simp
-/
lemma map_comp (g₁ : (i : ι) -> G i ->ₗ[R] G' i) (g₂ : (i : ι) -> G' i ->ₗ[R] G'' i)
    (hg₁ : forall i j h, g₁ j ∘ₗ f i j h = f' i j h ∘ₗ g₁ i)
    (hg₂ : forall i j h, g₂ j ∘ₗ f' i j h = f'' i j h ∘ₗ g₂ i) :
    (map g₂ hg₂ ∘ₗ map g₁ hg₁ :
      DirectLimit G f ->ₗ[R] DirectLimit G'' f'') =
    (map (fun i => g₂ i ∘ₗ g₁ i) fun i j h => by
        rw [LinearMap.comp_assoc]; rw [hg₁ i]; rw [← LinearMap.comp_assoc]; rw [hg₂ i]; rw [LinearMap.comp_assoc] :
      DirectLimit G f ->ₗ[R] DirectLimit G'' f'') := by
  ext; simp

open LinearEquiv LinearMap in
/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (e : (i : ι) -> G i ≃ₗ[R] G' i) (he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
  body: LinearEquiv.ofLinearMap (map (e ·) he)
    (map (fun i => (e i).symm) fun i j h => by
      rw [toLinearMap_symm_comp_eq]; rw [← comp_assoc]; rw [he i]; rw [comp_assoc]; rw [comp_coe]; rw [symm_trans_self]; rw [refl_toLinearMap]; rw [comp_id])
    (by simp [map_comp]) (by simp [map_comp])

中文:
定义 congr
  签名: (e : (i : ι) -> G i ≃ₗ[R] G' i) (he : 对任意 i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
  定义体: LinearEquiv.ofLinearMap (map (e ·) he)
    (map (fun i => (e i).symm) fun i j h => by
      rw [toLinearMap_symm_comp_eq]; rw [← comp_assoc]; rw [he i]; rw [comp_assoc]; rw [comp_coe]; rw [symm_trans_self]; rw [refl_toLinearMap]; rw [comp_id])
    (by simp [map_comp]) (by simp [map_comp])

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, comp_assoc, comp_coe, comp_id, map_comp, ofLinearMap, refl_toLinearMap, symm_trans_self, toLinearMap_symm_comp_eq
-/
def congr (e : (i : ι) -> G i ≃ₗ[R] G' i) (he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) :
    DirectLimit G f ≃ₗ[R] DirectLimit G' f' :=
  LinearEquiv.ofLinearMap (map (e ·) he)
    (map (fun i => (e i).symm) fun i j h => by
      rw [toLinearMap_symm_comp_eq]; rw [← comp_assoc]; rw [he i]; rw [comp_assoc]; rw [comp_coe]; rw [symm_trans_self]; rw [refl_toLinearMap]; rw [comp_id])
    (by simp [map_comp]) (by simp [map_comp])

/--
lemma `congr_apply_of` / 引理 `congr_apply_of`

English:
lemma congr_apply_of
  statement: (e : (i : ι) -> G i ≃ₗ[R] G' i) (he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
  proof: map_apply_of _ he _

中文:
引理 congr_apply_of
  结论: (e : (i : ι) -> G i ≃ₗ[R] G' i) (he : 对任意 i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
  证明: map_apply_of _ he _

Depends on / 依赖: map_apply_of
-/
lemma congr_apply_of (e : (i : ι) -> G i ≃ₗ[R] G' i) (he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
    {i : ι} (g : G i) :
    congr e he (of _ _ G f i g) = of _ _ G' f' i (e i g) :=
  map_apply_of _ he _

open LinearEquiv LinearMap in
/--
lemma `congr_symm_apply_of` / 引理 `congr_symm_apply_of`

English:
lemma congr_symm_apply_of
  statement: (e : (i : ι) -> G i ≃ₗ[R] G' i)
  proof: map_apply_of _ (fun i j h => by
    rw [toLinearMap_symm_comp_eq]; rw [← comp_assoc]; rw [he i]; rw [comp_assoc]; rw [comp_coe]; rw [symm_trans_self]; rw [refl_toLinearMap]; rw [comp_id]) _

中文:
引理 congr_symm_apply_of
  结论: (e : (i : ι) -> G i ≃ₗ[R] G' i)
  证明: map_apply_of _ (fun i j h => by
    rw [toLinearMap_symm_comp_eq]; rw [← comp_assoc]; rw [he i]; rw [comp_assoc]; rw [comp_coe]; rw [symm_trans_self]; rw [refl_toLinearMap]; rw [comp_id]) _

Depends on / 依赖: comp_assoc, comp_coe, comp_id, map_apply_of, refl_toLinearMap, symm_trans_self, toLinearMap_symm_comp_eq
-/
lemma congr_symm_apply_of (e : (i : ι) -> G i ≃ₗ[R] G' i)
    (he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) {i : ι} (g : G' i) :
    (congr e he).symm (of _ _ G' f' i g) = of _ _ G f i ((e i).symm g) :=
  map_apply_of _ (fun i j h => by
    rw [toLinearMap_symm_comp_eq]; rw [← comp_assoc]; rw [he i]; rw [comp_assoc]; rw [comp_coe]; rw [symm_trans_self]; rw [refl_toLinearMap]; rw [comp_id]) _

end functorial

end Basic

section equiv

variable [Nonempty ι] [IsDirectedOrder ι] [DirectedSystem G (f · · ·)]
open _root_.DirectLimit

/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: : DirectLimit G f ≃ₗ[R] _root_.DirectLimit G f
  body: .ofLinearMap
    (lift _ _ _ _ (Module.of _ _ _ _) fun _ _ _ _ => .symm <| eq_of_le ..)
    (Module.lift _ _ _ _ (of _ _ _ _) fun _ _ _ _ => of_f ..)
    (by ext; simp)
    (by ext; simp)

@[simp]

中文:
定义 linearEquiv
  签名: : DirectLimit G f ≃ₗ[R] _root_.DirectLimit G f
  定义体: .ofLinearMap
    (lift _ _ _ _ (Module.of _ _ _ _) fun _ _ _ _ => .symm <| eq_of_le ..)
    (Module.lift _ _ _ _ (of _ _ _ _) fun _ _ _ _ => of_f ..)
    (by ext; simp)
    (by ext; simp)

@[simp]

Depends on / 依赖: Module, Module.lift, Module.of, eq_of_le, ofLinearMap, of_f
-/
def linearEquiv : DirectLimit G f ≃ₗ[R] _root_.DirectLimit G f :=
  .ofLinearMap
    (lift _ _ _ _ (Module.of _ _ _ _) fun _ _ _ _ => .symm <| eq_of_le ..)
    (Module.lift _ _ _ _ (of _ _ _ _) fun _ _ _ _ => of_f ..)
    (by ext; simp)
    (by ext; simp)

@[simp]
/--
theorem `linearEquiv_of` / 定理 `linearEquiv_of`

English:
theorem linearEquiv_of
  given: {i g}
  statement: linearEquiv _ _ (of _ _ G f i g) = ⟦⟨i, g⟩⟧
  proof: by
  simp [linearEquiv]

@[simp]

中文:
定理 linearEquiv_of
  条件: {i g}
  结论: linearEquiv _ _ (of _ _ G f i g) = ⟦⟨i, g⟩⟧
  证明: by
  simp [linearEquiv]

@[simp]

Depends on / 依赖: linearEquiv
-/
theorem linearEquiv_of {i g} : linearEquiv _ _ (of _ _ G f i g) = ⟦⟨i, g⟩⟧ := by
  simp [linearEquiv]

@[simp]
/--
theorem `linearEquiv_symm_mk` / 定理 `linearEquiv_symm_mk`

English:
theorem linearEquiv_symm_mk
  given: {g}
  statement: (linearEquiv _ _).symm ⟦g⟧ = of _ _ G f g.1 g.2
  proof: rfl

中文:
定理 linearEquiv_symm_mk
  条件: {g}
  结论: (linearEquiv _ _).symm ⟦g⟧ = of _ _ G f g.1 g.2
  证明: rfl
-/
theorem linearEquiv_symm_mk {g} : (linearEquiv _ _).symm ⟦g⟧ = of _ _ G f g.1 g.2 := rfl

end equiv

variable {G f} [DirectedSystem G (f · · ·)] [IsDirectedOrder ι]

/--
theorem `exists_eq_of_of_eq` / 定理 `exists_eq_of_of_eq`

English:
theorem exists_eq_of_of_eq
  given: {i x y} (h : of R ι G f i x = of R ι G f i y)
  proof: by
  have := Nonempty.intro i
  apply_fun linearEquiv _ _ at h
  simp_rw [linearEquiv_of] at h
  have ⟨j, h⟩ := Quotient.exact h
  exact ⟨j, h.1, h.2.2⟩

中文:
定理 exists_eq_of_of_eq
  条件: {i x y} (h : of R ι G f i x = of R ι G f i y)
  证明: by
  have := Nonempty.intro i
  apply_fun linearEquiv _ _ at h
  simp_rw [linearEquiv_of] at h
  have ⟨j, h⟩ := Quotient.exact h
  exact ⟨j, h.1, h.2.2⟩

Depends on / 依赖: Nonempty, Nonempty.intro, Quotient, Quotient.exact, apply_fun, linearEquiv, linearEquiv_of, simp_rw
-/
theorem exists_eq_of_of_eq {i x y} (h : of R ι G f i x = of R ι G f i y) :
    exists j hij, f i j hij x = f i j hij y := by
  have := Nonempty.intro i
  apply_fun linearEquiv _ _ at h
  simp_rw [linearEquiv_of] at h
  have ⟨j, h⟩ := Quotient.exact h
  exact ⟨j, h.1, h.2.2⟩

/--
theorem `of.zero_exact` / 定理 `of.zero_exact`

English:
theorem of.zero_exact
  given: {i x} (H : of R ι G f i x = 0)
  proof: by
  convert! exists_eq_of_of_eq (H.trans (map_zero <| _).symm)
  rw [map_zero]

中文:
定理 of.zero_exact
  条件: {i x} (H : of R ι G f i x = 0)
  证明: by
  convert! exists_eq_of_of_eq (H.trans (map_zero <| _).symm)
  rw [map_zero]

Depends on / 依赖: H.trans, convert, exists_eq_of_of_eq, map_zero
-/
theorem of.zero_exact {i x} (H : of R ι G f i x = 0) :
    exists j hij, f i j hij x = (0 : G j) := by
  convert! exists_eq_of_of_eq (H.trans (map_zero <| _).symm)
  rw [map_zero]

end DirectLimit

end Module

namespace AddCommGroup

variable (G) [forall i, AddCommMonoid (G i)]

/--
Definition of `DirectLimit` / `DirectLimit` 的定义

English:
definition DirectLimit
  signature: [DecidableEq ι] (f : forall i j, i <= j -> G i ->+ G j)
  body: @Module.DirectLimit Nat _ ι _ G _ _ (fun i j hij => (f i j hij).toNatLinearMap) _
deriving AddCommMonoid, Inhabited

中文:
定义 DirectLimit
  签名: [DecidableEq ι] (f : 对任意 i j, i <= j -> G i ->+ G j)
  定义体: @Module.DirectLimit Nat _ ι _ G _ _ (fun i j hij => (f i j hij).toNatLinearMap) _
deriving AddCommMonoid, Inhabited

Depends on / 依赖: DirectLimit, Module, Module.DirectLimit, toNatLinearMap
-/
def DirectLimit [DecidableEq ι] (f : forall i j, i <= j -> G i ->+ G j) : Type _ :=
  @Module.DirectLimit Nat _ ι _ G _ _ (fun i j hij => (f i j hij).toNatLinearMap) _
deriving AddCommMonoid, Inhabited

namespace DirectLimit

variable (f : forall i j, i <= j -> G i ->+ G j)

local instance directedSystem [h : DirectedSystem G fun i j h => f i j h] :
    DirectedSystem G fun i j hij => (f i j hij).toNatLinearMap :=
  h

variable [DecidableEq ι]

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: (G : ι -> Type*) [forall i, AddCommGroup (G i)]
  body: inferInstanceAs AddCommGroup (Module.DirectLimit G _)

中文:
实例 addCommGroup
  签名: (G : ι -> 类型) [对任意 i, AddCommGroup (G i)]
  定义体: inferInstanceAs AddCommGroup (Module.DirectLimit G _)

Depends on / 依赖: AddCommGroup, DirectLimit, Module, Module.DirectLimit
-/
instance addCommGroup (G : ι -> Type*) [forall i, AddCommGroup (G i)]
    (f : forall i j, i <= j -> G i ->+ G j) : AddCommGroup (DirectLimit G f) :=
inferInstanceAs AddCommGroup (Module.DirectLimit G _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: ι] : Unique (DirectLimit G f)
  body: inferInstanceAs Unique (Module.DirectLimit G _)

中文:
实例 [IsEmpty
  签名: ι] : Unique (DirectLimit G f)
  定义体: inferInstanceAs Unique (Module.DirectLimit G _)

Depends on / 依赖: DirectLimit, Module, Module.DirectLimit, Unique
-/
instance [IsEmpty ι] : Unique (DirectLimit G f) :=
inferInstanceAs Unique (Module.DirectLimit G _)

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (i)
  body: (Module.DirectLimit.of Nat ι G _ i).toAddMonoidHom

中文:
定义 of
  签名: (i)
  定义体: (Module.DirectLimit.of Nat ι G _ i).toAddMonoidHom

Depends on / 依赖: DirectLimit, Module, Module.DirectLimit.of, toAddMonoidHom
-/
def of (i) : G i ->+ DirectLimit G f :=
  (Module.DirectLimit.of Nat ι G _ i).toAddMonoidHom

variable {G f}

@[simp]
/--
theorem `of_f` / 定理 `of_f`

English:
theorem of_f
  given: {i j} (hij) (x)
  statement: of G f j (f i j hij x) = of G f i x
  proof: Module.DirectLimit.of_f

@[elab_as_elim]

中文:
定理 of_f
  条件: {i j} (hij) (x)
  结论: of G f j (f i j hij x) = of G f i x
  证明: Module.DirectLimit.of_f

@[elab_as_elim]

Depends on / 依赖: DirectLimit, Module, Module.DirectLimit.of_f, of_f
-/
theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
  Module.DirectLimit.of_f

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f -> Prop}
  proof: Module.DirectLimit.induction_on z ih

中文:
定理 induction_on
  结论: [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f -> 命题}
  证明: Module.DirectLimit.induction_on z ih
-/
protected theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f -> Prop}
    (z : DirectLimit G f) (ih : forall i x, C (of G f i x)) : C z :=
  Module.DirectLimit.induction_on z ih

/--
theorem `of.zero_exact` / 定理 `of.zero_exact`

English:
theorem of.zero_exact
  statement: [IsDirectedOrder ι] [DirectedSystem G fun i j h => f i j h] (i x)
  proof: Module.DirectLimit.of.zero_exact h

中文:
定理 of.zero_exact
  结论: [IsDirectedOrder ι] [DirectedSystem G fun i j h => f i j h] (i x)
  证明: Module.DirectLimit.of.zero_exact h
-/
theorem of.zero_exact [IsDirectedOrder ι] [DirectedSystem G fun i j h => f i j h] (i x)
    (h : of G f i x = 0) : exists j hij, f i j hij x = 0 :=
  Module.DirectLimit.of.zero_exact h

variable (P : Type*) [AddCommMonoid P]
variable (g : forall i, G i ->+ P)
variable (Hg : forall i j hij x, g j (f i j hij x) = g i x)
variable (G f)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : DirectLimit G f ->+ P
  body: (Module.DirectLimit.lift Nat ι G (fun i j hij => (f i j hij).toNatLinearMap)
    (fun i => (g i).toNatLinearMap) Hg).toAddMonoidHom

中文:
定义 lift
  签名: : DirectLimit G f ->+ P
  定义体: (Module.DirectLimit.lift Nat ι G (fun i j hij => (f i j hij).toNatLinearMap)
    (fun i => (g i).toNatLinearMap) Hg).toAddMonoidHom

Depends on / 依赖: DirectLimit, Module, Module.DirectLimit.lift, toAddMonoidHom, toNatLinearMap
-/
def lift : DirectLimit G f ->+ P :=
  (Module.DirectLimit.lift Nat ι G (fun i j hij => (f i j hij).toNatLinearMap)
    (fun i => (g i).toNatLinearMap) Hg).toAddMonoidHom

variable {G f}

@[simp]
/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (i x)
  statement: lift G f P g Hg (of G f i x) = g i x
  proof: Module.DirectLimit.lift_of
    -- Note: had to make these arguments explicit https://github.com/leanprover-community/mathlib4/pull/8386
    (f := fun i j hij => (f i j hij).toNatLinearMap)
    (fun i => (g i).toNatLinearMap)
    Hg
    x

@[ext]

中文:
定理 lift_of
  条件: (i x)
  结论: lift G f P g Hg (of G f i x) = g i x
  证明: Module.DirectLimit.lift_of
    -- Note: had to make these arguments explicit https://github.com/leanprover-community/mathlib4/pull/8386
    (f := fun i j hij => (f i j hij).toNatLinearMap)
    (fun i => (g i).toNatLinearMap)
    Hg
    x

@[ext]

Depends on / 依赖: DirectLimit, Module, Module.DirectLimit.lift_of, lift_of
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  Module.DirectLimit.lift_of
    -- Note: had to make these arguments explicit https://github.com/leanprover-community/mathlib4/pull/8386
    (f := fun i j hij => (f i j hij).toNatLinearMap)
    (fun i => (g i).toNatLinearMap)
    Hg
    x

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {g₁ g₂ : DirectLimit G f ->+ P} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i))
  proof: AddCon.hom_ext DirectSum.addHom_ext' h

@[simp]

中文:
定理 hom_ext
  条件: {g₁ g₂ : DirectLimit G f ->+ P} (h : 对任意 i, g₁.comp (of G f i) = g₂.comp (of G f i))
  证明: AddCon.hom_ext DirectSum.addHom_ext' h

@[simp]

Depends on / 依赖: AddCon, AddCon.hom_ext, DirectSum, DirectSum.addHom_ext, addHom_ext, hom_ext
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f ->+ P} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ :=
AddCon.hom_ext DirectSum.addHom_ext' h

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: (F : DirectLimit G f ->+ P)
  proof: by
  ext; simp

@[simp]

中文:
定理 lift_comp_of
  条件: (F : DirectLimit G f ->+ P)
  证明: by
  ext; simp

@[simp]
-/
theorem lift_comp_of (F : DirectLimit G f ->+ P) :
    lift G f _ (fun i => F.comp <| of G f i) (fun i j hij x => by simp) = F := by
  ext; simp

@[simp]
/--
theorem `lift_of'` / 定理 `lift_of'`

English:
theorem lift_of'
  statement: lift G f _ (of G f) (fun i j hij x => by simp) = .id _
  proof: by
  ext; simp

中文:
定理 lift_of'
  结论: lift G f _ (of G f) (fun i j hij x => by simp) = .id _
  证明: by
  ext; simp
-/
theorem lift_of' : lift G f _ (of G f) (fun i j hij x => by simp) = .id _ := by
  ext; simp

/--
lemma `lift_injective` / 引理 `lift_injective`

English:
lemma lift_injective
  statement: [IsDirectedOrder ι]
  proof: Module.DirectLimit.lift_injective (f := fun i j hij => (f i j hij).toNatLinearMap) _ Hg injective

中文:
引理 lift_injective
  结论: [IsDirectedOrder ι]
  证明: Module.DirectLimit.lift_injective (f := fun i j hij => (f i j hij).toNatLinearMap) _ Hg injective

Depends on / 依赖: DirectLimit, Module, Module.DirectLimit.lift_injective, injective, lift_injective, toNatLinearMap
-/
lemma lift_injective [IsDirectedOrder ι]
    (injective : forall i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) :=
  Module.DirectLimit.lift_injective (f := fun i j hij => (f i j hij).toNatLinearMap) _ Hg injective

section functorial

variable {G' : ι -> Type*} [forall i, AddCommMonoid (G' i)]
variable {f' : forall i j, i <= j -> G' i ->+ G' j}
variable {G'' : ι -> Type*} [forall i, AddCommMonoid (G'' i)]
variable {f'' : forall i j, i <= j -> G'' i ->+ G'' j}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (g : (i : ι) -> G i ->+ G' i)
  body: lift _ _ _ (fun i => (of _ _ _).comp (g i)) fun i j h g => by
    have eq1 := DFunLike.congr_fun (hg i j h) g
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1]; rw [of_f]

中文:
定义 map
  签名: (g : (i : ι) -> G i ->+ G' i)
  定义体: lift _ _ _ (fun i => (of _ _ _).comp (g i)) fun i j h g => by
    have eq1 := DFunLike.congr_fun (hg i j h) g
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1]; rw [of_f]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_comp, DFunLike, DFunLike.congr_fun, Function, Function.comp_apply, coe_comp, comp_apply, congr_fun, of_f
-/
def map (g : (i : ι) -> G i ->+ G' i)
    (hg : forall i j h, (g j).comp (f i j h) = (f' i j h).comp (g i)) :
    DirectLimit G f ->+ DirectLimit G' f' :=
  lift _ _ _ (fun i => (of _ _ _).comp (g i)) fun i j h g => by
    have eq1 := DFunLike.congr_fun (hg i j h) g
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1]; rw [of_f]

/--
lemma `map_apply_of` / 引理 `map_apply_of`

English:
lemma map_apply_of
  statement: (g : (i : ι) -> G i ->+ G' i)
  proof: lift_of _ _ _ _ _

中文:
引理 map_apply_of
  结论: (g : (i : ι) -> G i ->+ G' i)
  证明: lift_of _ _ _ _ _
-/
@[simp] lemma map_apply_of (g : (i : ι) -> G i ->+ G' i)
    (hg : forall i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G f _ x) = of G' f' i (g i x) :=
  lift_of _ _ _ _ _

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  proof: by
  ext; simp

中文:
引理 map_id
  证明: by
  ext; simp
-/
@[simp] lemma map_id :
    map (fun _ => AddMonoidHom.id _) (fun _ _ _ => rfl) = AddMonoidHom.id (DirectLimit G f) := by
  ext; simp

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: (g₁ : (i : ι) -> G i ->+ G' i) (g₂ : (i : ι) -> G' i ->+ G'' i)
  proof: by
  ext; simp

中文:
引理 map_comp
  结论: (g₁ : (i : ι) -> G i ->+ G' i) (g₂ : (i : ι) -> G' i ->+ G'' i)
  证明: by
  ext; simp
-/
lemma map_comp (g₁ : (i : ι) -> G i ->+ G' i) (g₂ : (i : ι) -> G' i ->+ G'' i)
    (hg₁ : forall i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : forall i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G f ->+ DirectLimit G'' f'') =
    (map (fun i => (g₂ i).comp (g₁ i)) fun i j h => by
      rw [AddMonoidHom.comp_assoc]; rw [hg₁ i]; rw [← AddMonoidHom.comp_assoc]; rw [hg₂ i]; rw [AddMonoidHom.comp_assoc] :
      DirectLimit G f ->+ DirectLimit G'' f'') := by
  ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (e : (i : ι) -> G i ≃+ G' i)
  body: AddMonoidHom.toAddEquiv (map (e ·) he)
    (map (fun i => (e i).symm) fun i j h => DFunLike.ext _ _ fun x => by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
        AddMonoidHom.coe_coe, AddEq

中文:
定义 congr
  签名: (e : (i : ι) -> G i ≃+ G' i)
  定义体: AddMonoidHom.toAddEquiv (map (e ·) he)
    (map (fun i => (e i).symm) fun i j h => DFunLike.ext _ _ fun x => by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
        AddMonoidHom.coe_coe, AddEq

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, AddEquiv.coe_toAddMonoidHom, AddMonoidHom, AddMonoidHom.coe_coe, AddMonoidHom.coe_comp, AddMonoidHom.toAddEquiv, DFunLike, DFunLike.congr_fun, DFunLike.ext, Function, Function.comp_apply, apply_symm_apply, coe_coe, coe_comp, coe_toAddMonoidHom, comp_apply, congr_fun, map_comp, toAddEquiv
-/
def congr (e : (i : ι) -> G i ≃+ G' i)
    (he : forall i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G f ≃+ DirectLimit G' f' :=
  AddMonoidHom.toAddEquiv (map (e ·) he)
    (map (fun i => (e i).symm) fun i j h => DFunLike.ext _ _ fun x => by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
        AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1])
    (by simp [map_comp]) (by simp [map_comp])

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `congr_apply_of` / 引理 `congr_apply_of`

English:
lemma congr_apply_of
  statement: (e : (i : ι) -> G i ≃+ G' i)
  proof: map_apply_of _ he _

中文:
引理 congr_apply_of
  结论: (e : (i : ι) -> G i ≃+ G' i)
  证明: map_apply_of _ he _

Depends on / 依赖: map_apply_of
-/
lemma congr_apply_of (e : (i : ι) -> G i ≃+ G' i)
    (he : forall i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G f i g) = of G' f' i (e i g) :=
  map_apply_of _ he _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `congr_symm_apply_of` / 引理 `congr_symm_apply_of`

English:
lemma congr_symm_apply_of
  statement: (e : (i : ι) -> G i ≃+ G' i)
  proof: by
  simp only [congr, AddMonoidHom.toAddEquiv_symm_apply, map_apply_of, AddMonoidHom.coe_coe]

中文:
引理 congr_symm_apply_of
  结论: (e : (i : ι) -> G i ≃+ G' i)
  证明: by
  simp only [congr, AddMonoidHom.toAddEquiv_symm_apply, map_apply_of, AddMonoidHom.coe_coe]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, AddMonoidHom.toAddEquiv_symm_apply, coe_coe, map_apply_of, toAddEquiv_symm_apply
-/
lemma congr_symm_apply_of (e : (i : ι) -> G i ≃+ G' i)
    (he : forall i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' f' i g) = of G f i ((e i).symm g) := by
  simp only [congr, AddMonoidHom.toAddEquiv_symm_apply, map_apply_of, AddMonoidHom.coe_coe]

end functorial

end DirectLimit

end AddCommGroup
