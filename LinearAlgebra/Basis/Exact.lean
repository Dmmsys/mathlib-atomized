/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Basis from a split exact sequence

Let `0 → K → M → P → 0` be a split exact sequence of `R`-modules, let `s : M → K` be a
retraction of `f` and `v` be a basis of `M` indexed by `κ ⊕ σ`. Then
if `s vᵢ = 0` for `i : κ` and `(s vⱼ)ⱼ` is linear independent for `j : σ`, then
the images of `vᵢ` for `i : κ` form a basis of `P`.

We treat linear independence and the span condition separately. For convenience this
is stated not for `κ ⊕ σ`, but for an arbitrary type `ι` with two maps `κ → ι` and `σ → ι`.
-/

@[expose] public section

variable {R M K P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup K] [AddCommGroup P]
variable [Module R M] [Module R K] [Module R P]
variable {f : K →ₗ[R] M} {g : M →ₗ[R] P} {s : M →ₗ[R] K}
variable (hs : s ∘ₗ f = LinearMap.id) (hfg : Function.Exact f g)
variable {ι κ σ : Type*} {v : ι → M} {a : κ → ι} {b : σ → ι}

section
include hs hfg

/-
**LinearIndependent.linearIndependent_of_exact_of_retraction** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：LinearIndependent.linearIndependent_of_exact_of_retraction (hainj : Functi
on.Injective a) (hsa : forall i, s (v (a i)) = 0) (hli : LinearIndependent R v) 
: LinearIndependent R (g ∘ v ∘ a)
参数：hainj : Function.Injective a；hsa : forall i, s (v (a i)) = 0；hli : LinearInde
pendent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.map`：LinearIndependent.map (hv : LinearIndependent R v
) {f : M ->ₗ[R] M'} (hf_inj : Disjoint (span R (range v)) (LinearMap.ker f)) : L
inearIndepe…
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma LinearIndependent.linearIndependent_of_exact_of_retraction
    (hainj : Function.Injective a) (hsa : ∀ i, s (v (a i)) = 0)
    (hli : LinearIndependent R v) :
    LinearIndependent R (g ∘ v ∘ a) := by
  apply (LinearIndependent.comp hli a hainj).map
  rw [Submodule.disjoint_def, hfg.linearMap_ker_eq]
  rintro - hy ⟨y, rfl⟩
  have hz : s (f y) = 0 := by
    revert hy
    generalize f y = x
    intro hy
    induction hy using Submodule.span_induction with
    | mem m hm => obtain ⟨i, rfl⟩ := hm; apply hsa
    | zero => simp_all
    | add => simp_all
    | smul => simp_all
  replace hs := DFunLike.congr_fun hs y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
  rw [← hs, hz, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**top_le_span_of_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma top_le_span_of_aux (v : κ ⊕ σ → M)
    (hg : Function.Surjective g) (hslzero : ∀ i, s (v (.inl i)) = 0)
    (hli : LinearIndependent R (s ∘ v ∘ .inr)) (hsp : ⊤ ≤ Submodule.span R (Set.range v)) :
    ⊤ ≤ Submodule.span R (Set.range <| g ∘ v ∘ .inl) := by
  rintro p -
  obtain ⟨m, rfl⟩ := hg p
  wlog h : m ∈ LinearMap.ker s
  · let x : M := f (s m)
    rw [show g m = g (m - f (s m)) by simp [hfg.apply_apply_eq_zero]]
    apply this hs hfg v hg hslzero hli hsp
    replace hs := DFunLike.congr_fun hs (s m)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
    simp [hs]
  have : m ∈ Submodule.span R (Set.range v) := hsp Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp this
  simp only [LinearMap.mem_ker, Finsupp.sum, map_sum, map_smul,
    Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, map_add, hslzero, smul_zero,
    Finset.sum_const_zero, zero_add] at h
  replace hli := (linearIndependent_iff'.mp hli) c.support.toRight (c ∘ .inr) h
  simp only [Finset.mem_toRight, Finsupp.mem_support_iff, Function.comp_apply, not_imp_self] at hli
  simp only [Finsupp.sum, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hli, zero_smul,
    Finset.sum_const_zero, add_zero, map_sum, map_smul]
  exact Submodule.sum_mem _ (fun i hi ↦ Submodule.smul_mem _ _ <| Submodule.subset_span ⟨i, rfl⟩)
/-
**Submodule.top_le_span_of_exact_of_retraction** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.top_le_span_of_exact_of_retraction (hg : Function.Surjective g) 
(hsa : forall i, s (v (a i)) = 0) (hlib : LinearIndependent R (s ∘ v ∘ b)) (hab 
: Codisjoint (Set.range a) (Set.range b)) (hsp : ⊤ <= Submodule.span R (Set.rang
e v)) : ⊤ <= Submodule.span R (Set.range <| g ∘ v ∘ a)
参数：hg : Function.Surjective g；hsa : forall i, s (v (a i)) = 0；hlib : LinearIndep
endent R (s ∘ v ∘ b)；hab : Codisjoint (Set.range a) (Set.range b)；hsp : ⊤ <= Sub
module.span R (Set.range v)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.LinearAlgebra.Basis.Exact.0.top_le_span_of_aux`：∀ {R : 
Type u_1} {M : Type u_2} {K : Type u_3} {P : Type u_4} [inst : Ring R] [inst_1 :
 AddCommGroup M]   [inst_2 : AddCommGroup K] [inst_3 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Sum.elim_range`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : 
α → γ) (g : β → γ),   Set.range (Sum.elim f g) = Set.range f ∪ Set.range g
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
lemma Submodule.top_le_span_of_exact_of_retraction (hg : Function.Surjective g)
    (hsa : ∀ i, s (v (a i)) = 0) (hlib : LinearIndependent R (s ∘ v ∘ b))
    (hab : Codisjoint (Set.range a) (Set.range b))
    (hsp : ⊤ ≤ Submodule.span R (Set.range v)) :
    ⊤ ≤ Submodule.span R (Set.range <| g ∘ v ∘ a) := by
  apply top_le_span_of_aux hs hfg (Sum.elim (v ∘ a) (v ∘ b)) hg hsa hlib
  simp only [codisjoint_iff, Set.sup_eq_union, Set.top_eq_univ] at hab
  rwa [Set.Sum.elim_range, Set.range_comp, Set.range_comp, ← Set.image_union, hab, Set.image_univ]

/-- Let `0 → K → M → P → 0` be a split exact sequence of `R`-modules, let `s : M → K` be a
retraction of `f` and `v` be a basis of `M` indexed by `κ ⊕ σ`. Then
if `s vᵢ = 0` for `i : κ` and `(s vⱼ)ⱼ` is linear independent for `j : σ`, then
the images of `vᵢ` for `i : κ` form a basis of `P`.

For convenience this is stated for an arbitrary type `ι` with two maps `κ → ι` and `σ → ι`. -/
/-
**Module.Basis.ofSplitExact** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.Basis.ofSplitExact (hg : Function.Surjective g) (v : Basis ι R M) (
hainj : Function.Injective a) (hsa : forall i, s (v (a i)) = 0) (hlib : LinearIn
dependent R (s ∘ v ∘ b)) (hab : Codisjoint (Set.range a) (Set.range b)) : Basis 
κ R P
参数：hg : Function.Surjective g；v : Basis ι R M；hainj : Function.Injective a；hsa :
 forall i, s (v (a i)) = 0；hlib : LinearIndependent R (s ∘ v ∘ b)；hab : Codisjoi
nt (Set.range a) (Set.range b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `0 → K → M → P → 0` be a split exact sequence of `R`-modules, let `s : M → K
` be a
retraction of `f` and `v` be a basis of `M` indexed by `κ ⊕ σ`. Then
if `s vᵢ = 0` for `i : κ` and `(s vⱼ)ⱼ` is linear independent for `j : σ`, then
the images of `vᵢ` for `i : κ` form a basis of `P`.

For convenience this is stated for an arbitrary type `ι` with two maps `κ → ι` a
nd `σ → ι`.
-/
noncomputable def Module.Basis.ofSplitExact (hg : Function.Surjective g) (v : Basis ι R M)
    (hainj : Function.Injective a) (hsa : ∀ i, s (v (a i)) = 0)
    (hlib : LinearIndependent R (s ∘ v ∘ b))
    (hab : Codisjoint (Set.range a) (Set.range b)) :
    Basis κ R P :=
  .mk (v.linearIndependent.linearIndependent_of_exact_of_retraction hs hfg hainj hsa)
    (Submodule.top_le_span_of_exact_of_retraction hs hfg hg hsa hlib hab (by rw [v.span_eq]))

@[simp]
/-
**Module.Basis.ofSplitExact_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Basis.ofSplitExact_apply (hg : Function.Surjective g) (v : Basis ι 
R M) (hainj : Function.Injective a) (hsa : forall i, s (v (a i)) = 0) (hlib : Li
nearIndependent R (s ∘ v ∘ b)) (hab : Codisjoint (Set.range a) (Set.range b)) (k
 : κ) : ofSplitExact hs hfg hg v hainj hsa hlib hab k = g (v (a k))
参数：hg : Function.Surjective g；v : Basis ι R M；hainj : Function.Injective a；hsa :
 forall i, s (v (a i)) = 0；hlib : LinearIndependent R (s ∘ v ∘ b)；hab : Codisjoi
nt (Set.range a) (Set.range b)；k : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Module.Basis.ofSplitExact_apply (hg : Function.Surjective g) (v : Basis ι R M)
    (hainj : Function.Injective a) (hsa : ∀ i, s (v (a i)) = 0)
    (hlib : LinearIndependent R (s ∘ v ∘ b))
    (hab : Codisjoint (Set.range a) (Set.range b)) (k : κ) :
    ofSplitExact hs hfg hg v hainj hsa hlib hab k = g (v (a k)) := by
  simp [ofSplitExact]

end

section
include hfg

/-
**Submodule.projectionOnto_comp_surjective_of_exact** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：Submodule.projectionOnto_comp_surjective_of_exact {p q : Submodule R M} (h
pq : IsCompl p q) (hmap : Submodule.map g q = ⊤) : Function.Surjective (Submodul
e.projectionOnto p q hpq ∘ₗ f)
参数：hpq : IsCompl p q；hmap : Submodule.map g q = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.surjOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.SurjOn
 f Set.univ Set.univ ↔ Function.Surjective f
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用引理 `Set.surjOn_comp_iff`：surjOn_comp_iff : SurjOn (g ∘ f) s p ↔ SurjOn g (f 
'' s) p
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `Submodule.top_coe`：top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ
· 使用引理 `Submodule.surjOn_iff_le_map`：surjOn_iff_le_map [RingHomSurjective τ₁₂] {
f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂} : Set.SurjOn f p q
 ↔ q <= p.map f
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
-/
lemma Submodule.projectionOnto_comp_surjective_of_exact
    {p q : Submodule R M} (hpq : IsCompl p q)
    (hmap : Submodule.map g q = ⊤) :
    Function.Surjective (Submodule.projectionOnto p q hpq ∘ₗ f) := by
  rw [← Set.surjOn_univ, LinearMap.coe_comp, Set.surjOn_comp_iff, Set.image_univ]
  rw [← LinearMap.coe_range, ← Submodule.top_coe (R := R), surjOn_iff_le_map,
    ← hfg.linearMap_ker_eq]
  intro x triv
  obtain ⟨a, haq, ha⟩ : g x.val ∈ q.map g := by rwa [hmap]
  exact ⟨x - a, by simp [← ha], by simpa⟩

@[deprecated (since := "2026-05-05")] alias
  Submodule.linearProjOfIsCompl_comp_surjective_of_exact :=
  Submodule.projectionOnto_comp_surjective_of_exact
/-
**Submodule.projectionOnto_comp_bijective_of_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.projectionOnto_comp_bijective_of_exact (hf : Function.Injective 
f) {p q : Submodule R M} (hpq : IsCompl p q) (hker : Disjoint (LinearMap.ker g) 
q) (hmap : Submodule.map g q = ⊤) : Function.Bijective (Submodule.projectionOnto
 p q hpq ∘ₗ f)
参数：hf : Function.Injective f；hpq : IsCompl p q；hker : Disjoint (LinearMap.ker g)
 q；hmap : Submodule.map g q = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Set.InjOn.injective_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : α → β} {g : β → γ} (s : Set β),   Set.InjOn g s → Set.range f ⊆ s → (Functi
on.Injective …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `Submodule.ker_projectionOnto`：ker_projectionOnto (h : IsCompl p q) : ker
 (projectionOnto p q h) = q
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用引理 `Submodule.projectionOnto_comp_surjective_of_exact`：Submodule.projectionO
nto_comp_surjective_of_exact {p q : Submodule R M} (hpq : IsCompl p q) (hmap : S
ubmodule.map g q = ⊤) : Function.Surjec…
-/
lemma Submodule.projectionOnto_comp_bijective_of_exact
    (hf : Function.Injective f) {p q : Submodule R M} (hpq : IsCompl p q)
    (hker : Disjoint (LinearMap.ker g) q) (hmap : Submodule.map g q = ⊤) :
    Function.Bijective (Submodule.projectionOnto p q hpq ∘ₗ f) := by
  refine ⟨?_, Submodule.projectionOnto_comp_surjective_of_exact hfg _ hmap⟩
  rwa [LinearMap.coe_comp, Set.InjOn.injective_iff ↑(LinearMap.range f) _ subset_rfl]
  simpa [← LinearMap.disjoint_ker_iff_injOn, ← hfg.linearMap_ker_eq]

@[deprecated (since := "2026-05-05")] alias
  Submodule.linearProjOfIsCompl_comp_bijective_of_exact :=
  Submodule.projectionOnto_comp_bijective_of_exact
/-
**LinearMap.linearProjOfIsCompl_comp_bijective_of_exact** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：LinearMap.linearProjOfIsCompl_comp_bijective_of_exact (hf : Function.Injec
tive f) {q : Submodule R M} {E : Type*} [AddCommGroup E] [Module R E] {i : E ->ₗ
[R] M} (hi : Function.Injective i) (h : IsCompl (LinearMap.range i) q) (hker : D
isjoint (LinearMap.ker g) q) (hmap : Submodule.map g q = ⊤) : Function.Bijective
 (LinearMap.linearProjOfIsCompl q i hi h ∘ₗ f)
参数：hf : Function.Injective f；hi : Function.Injective i；h : IsCompl (LinearMap.ra
nge i) q；hker : Disjoint (LinearMap.ker g) q；hmap : Submodule.map g q = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.linearProjOfIsCompl.eq_1`：∀ {R : Type u_1} [inst : Ring R] {E 
: Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (q : Submod
ule R E) {F : Type u_7} …
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用引理 `Submodule.projectionOnto_comp_bijective_of_exact`：Submodule.projectionOn
to_comp_bijective_of_exact (hf : Function.Injective f) {p q : Submodule R M} (hp
q : IsCompl p q) (hker : Disjoint (Lin…
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
lemma LinearMap.linearProjOfIsCompl_comp_bijective_of_exact
    (hf : Function.Injective f) {q : Submodule R M} {E : Type*} [AddCommGroup E] [Module R E]
    {i : E →ₗ[R] M} (hi : Function.Injective i) (h : IsCompl (LinearMap.range i) q)
    (hker : Disjoint (LinearMap.ker g) q) (hmap : Submodule.map g q = ⊤) :
    Function.Bijective (LinearMap.linearProjOfIsCompl q i hi h ∘ₗ f) := by
  rw [LinearMap.linearProjOfIsCompl, LinearMap.comp_assoc, LinearMap.coe_comp,
      Function.Bijective.of_comp_iff]
  · exact (LinearEquiv.ofInjective i hi).symm.bijective
  · exact Submodule.projectionOnto_comp_bijective_of_exact hfg hf h hker hmap

end

