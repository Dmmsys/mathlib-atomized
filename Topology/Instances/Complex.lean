/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Some results about the topology of ℂ
-/

public section


section ComplexSubfield

open Complex Set

open ComplexConjugate

/-- The only closed subfields of `ℂ` are `ℝ` and `ℂ`. -/
/-
**Complex.subfield_eq_of_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.subfield_eq_of_closed {K : Subfield Complex} (hc : IsClosed (K : S
et Complex)) : K = ofRealHom.fieldRange ∨ K = ⊤
参数：hc : IsClosed (K : Set Complex)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `DenseRange.closure_range`：DenseRange.closure_range (h : DenseRange f) : 
closure (range f) = univ
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `IsDenseEmbedding.toIsDenseInducing`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbe
dding e → IsDenseInducin…
· 使用定理 `Rat.isDenseEmbedding_coe_real`：isDenseEmbedding_coe_real : IsDenseEmbedd
ing ((↑) : Rat -> Real)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `Complex.coe_algebraMap`：coe_algebraMap : (algebraMap Real Complex : Real
 -> Complex) = ((↑) : Real -> Complex)
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `Subalgebra.isSimpleOrder_of_finrank`：Subalgebra.isSimpleOrder_of_finrank
 (hr : finrank F E = 2) : IsSimpleOrder (Subalgebra F E)
· 使用定理 `Complex.finrank_real_complex`：finrank_real_complex : finrank Real Comple
x = 2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
The only closed subfields of `ℂ` are `ℝ` and `ℂ`.
-/
theorem Complex.subfield_eq_of_closed {K : Subfield ℂ} (hc : IsClosed (K : Set ℂ)) :
    K = ofRealHom.fieldRange ∨ K = ⊤ := by
  suffices range (ofReal : ℝ → ℂ) ⊆ K by
    rw [range_subset_iff, ← coe_algebraMap] at this
    have :=
      (Subalgebra.isSimpleOrder_of_finrank finrank_real_complex).eq_bot_or_eq_top
        (Subfield.toIntermediateField K this).toSubalgebra
    simp_rw [← SetLike.coe_set_eq, IntermediateField.coe_toSubalgebra] at this ⊢
    exact this
  suffices range (ofReal : ℝ → ℂ) ⊆ closure (Set.range ((ofReal : ℝ → ℂ) ∘ ((↑) : ℚ → ℝ))) by
    refine subset_trans this ?_
    rw [← IsClosed.closure_eq hc]
    apply closure_mono
    rintro _ ⟨_, rfl⟩
    simp only [Function.comp_apply, ofReal_ratCast, SetLike.mem_coe, SubfieldClass.ratCast_mem]
  nth_rw 1 [range_comp]
  refine subset_trans ?_ (image_closure_subset_closure_image continuous_ofReal)
  rw [DenseRange.closure_range Rat.isDenseEmbedding_coe_real.dense]
  simp only [image_univ]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `K` a subfield of `ℂ` and let `ψ : K →+* ℂ` a ring homomorphism. Assume that `ψ` is uniform
continuous, then `ψ` is either the inclusion map or the composition of the inclusion map with the
complex conjugation. -/
/-
**Complex.uniformContinuous_ringHom_eq_id_or_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.uniformContinuous_ringHom_eq_id_or_conj (K : Subfield Complex) {ψ 
: K ->+* Complex} (hc : UniformContinuous ψ) : ψ.toFun = K.subtype ∨ ψ.toFun = c
onj ∘ K.subtype
参数：K : Subfield Complex；hc : UniformContinuous ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `Subfield.le_topologicalClosure`：Subfield.le_topologicalClosure (s : Subf
ield α) : s <= s.topologicalClosure
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_subtype`：uniformity_subtype {p : α -> Prop} [UniformSpace α] 
: 𝓤 (Subtype p) = comap (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用引理 `IsUniformInducing.isDenseInducing`：IsUniformInducing.isDenseInducing (h 
: IsUniformInducing f) (hd : DenseRange f) : IsDenseInducing f where toIsInducin
g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `DenseRange.comp`：DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRa
nge g) (hf : DenseRange f) (cg : Continuous g) : DenseRange (g ∘ f)
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `IsDenseEmbedding.toIsDenseInducing`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbe
dding e → IsDenseInducin…
· 使用定理 `IsDenseEmbedding.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbedding e → 
∀ (p : α → Pro…
· 使用定理 `IsDenseEmbedding.id`：∀ {α : Type u_5} [inst : TopologicalSpace α], IsDen
seEmbedding id
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `uniformContinuous_uniformly_extend`：uniformContinuous_uniformly_extend [
CompleteSpace γ] : UniformContinuous ψ
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K` a subfield of `ℂ` and let `ψ : K →+* ℂ` a ring homomorphism. Assume that
 `ψ` is uniform
continuous, then `ψ` is either the inclusion map or the composition of the inclu
sion map with the
complex conjugation.
-/
theorem Complex.uniformContinuous_ringHom_eq_id_or_conj (K : Subfield ℂ) {ψ : K →+* ℂ}
    (hc : UniformContinuous ψ) : ψ.toFun = K.subtype ∨ ψ.toFun = conj ∘ K.subtype := by
  let : IsTopologicalDivisionRing ℂ := IsTopologicalDivisionRing.mk
  let : IsTopologicalRing K.topologicalClosure :=
    Subring.instIsTopologicalRing K.topologicalClosure.toSubring
  set ι : K → K.topologicalClosure := ⇑(Subfield.inclusion K.le_topologicalClosure)
  have ui : IsUniformInducing ι :=
    ⟨by
      rw [uniformity_subtype, uniformity_subtype, Filter.comap_comap]
      congr ⟩
  let di := ui.isDenseInducing (?_ : DenseRange ι)
  · -- extψ : closure(K) →+* ℂ is the extension of ψ : K →+* ℂ
    let extψ := IsDenseInducing.extendRingHom ui di.dense hc
    have hψ := (uniformContinuous_uniformly_extend ui di.dense hc).continuous
    rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure K) with h | h
    · left
      let j := RingEquiv.subfieldCongr h
      -- ψ₁ is the continuous ring hom `ℝ →+* ℂ` constructed from `j : closure (K) ≃+* ℝ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ := RingHom.comp extψ (RingHom.comp j.symm.toRingHom ofRealHom.rangeRestrictField)
      -- Porting note: was `by continuity!` and was used inline
      have hψ₁ : Continuous ψ₁ := by
        simpa only [RingHom.coe_comp] using! hψ.comp ((continuous_algebraMap ℝ ℂ).subtype_mk _)
      ext1 x
      rsuffices ⟨r, hr⟩ : ∃ r : ℝ, ofRealHom.rangeRestrictField r = j (ι x)
      · have := RingHom.congr_fun (ringHom_eq_ofReal_of_continuous hψ₁) r
        rw [RingHom.comp_apply, RingHom.comp_apply, hr, RingEquiv.toRingHom_eq_coe] at this
        convert! this using 1
        · exact (IsDenseInducing.extend_eq di hc.continuous _).symm
        · rw [← ofRealHom.coe_rangeRestrictField, hr]
          rfl
      obtain ⟨r, hr⟩ := SetLike.coe_mem (j (ι x))
      exact ⟨r, Subtype.ext hr⟩
    · -- ψ₁ is the continuous ring hom `ℂ →+* ℂ` constructed from `closure (K) ≃+* ℂ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ :=
        RingHom.comp extψ
          (RingHom.comp (RingEquiv.subfieldCongr h).symm.toRingHom
            (@Subfield.topEquiv ℂ _).symm.toRingHom)
      -- Porting note: was `by continuity!` and was used inline
      have hψ₁ : Continuous ψ₁ := by
        simpa only [RingHom.coe_comp] using! hψ.comp (continuous_id.subtype_mk _)
      rcases ringHom_eq_id_or_conj_of_continuous hψ₁ with h | h
      · left
        ext1 z
        convert! RingHom.congr_fun h z using 1
        exact (IsDenseInducing.extend_eq di hc.continuous z).symm
      · right
        ext1 z
        convert! RingHom.congr_fun h z using 1
        exact (IsDenseInducing.extend_eq di hc.continuous z).symm
  · let j : { x // x ∈ closure (id '' K) } → (K.topologicalClosure : Set ℂ) :=
      fun x =>
      ⟨x, by
        convert! x.prop
        simp only [id, Set.image_id']
        rfl ⟩
    convert!
      DenseRange.comp (Function.Surjective.denseRange _) (IsDenseEmbedding.id.subtype (· ∈ K)).dense
        (by fun_prop : Continuous j)
    rintro ⟨y, hy⟩
    use
      ⟨y, by
        convert! hy
        simp only [id, Set.image_id']
        rfl ⟩

end ComplexSubfield

