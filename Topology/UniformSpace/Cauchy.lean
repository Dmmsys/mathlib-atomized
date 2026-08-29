/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Bases
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-!
# Theory of Cauchy filters in uniform spaces. Complete uniform spaces. Totally bounded subsets.
-/

@[expose] public section

universe u v

open Filter Function TopologicalSpace Topology Set UniformSpace Uniformity
open scoped SetRel

variable {α : Type u} {β : Type v} [uniformSpace : UniformSpace α]

/--
Definition of `Cauchy` / `Cauchy` 的定义

English:
definition Cauchy
  signature: (f : Filter α)
  body: NeBot f ∧ f ×ˢ f <= 𝓤 α

中文:
定义 Cauchy
  签名: (f : Filter α)
  定义体: NeBot f ∧ f ×ˢ f <= 𝓤 α
-/
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f <= 𝓤 α

/--
Definition of `IsComplete` / `IsComplete` 的定义

English:
definition IsComplete
  signature: (s : Set α)
  body: forall f, Cauchy f -> f <= 𝓟 s -> exists x in s, f <= 𝓝 x

中文:
定义 IsComplete
  签名: (s : Set α)
  定义体: forall f, Cauchy f -> f <= 𝓟 s -> exists x in s, f <= 𝓝 x

Depends on / 依赖: Cauchy
-/
def IsComplete (s : Set α) :=
  forall f, Cauchy f -> f <= 𝓟 s -> exists x in s, f <= 𝓝 x

/--
theorem `Filter.HasBasis.cauchy_iff` / 定理 `Filter.HasBasis.cauchy_iff`

English:
theorem Filter.HasBasis.cauchy_iff
  statement: {ι} {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
  proof: and_congr Iff.rfl
(f.basis_sets.prod_self.le_basis_iff h).trans by
      simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, id, forall_mem_comm]

中文:
定理 Filter.HasBasis.cauchy_iff
  结论: {ι} {p : ι -> 命题} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
  证明: and_congr Iff.rfl
(f.basis_sets.prod_self.le_basis_iff h).trans by
      simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, id, forall_mem_comm]

Depends on / 依赖: Iff.rfl, Prod.forall, and_congr, and_imp, basis_sets, f.basis_sets.prod_self.le_basis_iff, forall_mem_comm, le_basis_iff, mem_prod_eq, prod_self, subset_def
-/
theorem Filter.HasBasis.cauchy_iff {ι} {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
    {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ forall i, p i -> exists t in f, forall x in t, forall y in t, (x, y) in s i :=
and_congr Iff.rfl
(f.basis_sets.prod_self.le_basis_iff h).trans by
      simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, id, forall_mem_comm]

/--
theorem `cauchy_iff'` / 定理 `cauchy_iff'`

English:
theorem cauchy_iff'
  given: {f : Filter α}
  proof: (𝓤 α).basis_sets.cauchy_iff

中文:
定理 cauchy_iff'
  条件: {f : Filter α}
  证明: (𝓤 α).basis_sets.cauchy_iff

Depends on / 依赖: basis_sets, basis_sets.cauchy_iff, cauchy_iff
-/
theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ forall s in 𝓤 α, exists t in f, forall x in t, forall y in t, (x, y) in s :=
  (𝓤 α).basis_sets.cauchy_iff

/--
theorem `cauchy_iff` / 定理 `cauchy_iff`

English:
theorem cauchy_iff
  given: {f : Filter α}
  statement: Cauchy f ↔ NeBot f ∧ forall s in 𝓤 α, exists t in f, t ×ˢ t subseteq s
  proof: cauchy_iff'.trans by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]

中文:
定理 cauchy_iff
  条件: {f : Filter α}
  结论: Cauchy f ↔ NeBot f ∧ 对任意 s in 𝓤 α, 存在 t in f, t ×ˢ t subseteq s
  证明: cauchy_iff'.trans by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]

Depends on / 依赖: Prod.forall, and_imp, cauchy_iff, forall_mem_comm, mem_prod_eq, subset_def
-/
theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ forall s in 𝓤 α, exists t in f, t ×ˢ t subseteq s :=
cauchy_iff'.trans by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]

/--
lemma `cauchy_iff_le` / 引理 `cauchy_iff_le`

English:
lemma cauchy_iff_le
  given: {l : Filter α} [hl : l.NeBot]
  proof: by
  simp only [Cauchy, hl, true_and]

中文:
引理 cauchy_iff_le
  条件: {l : Filter α} [hl : l.NeBot]
  证明: by
  simp only [Cauchy, hl, true_and]

Depends on / 依赖: Cauchy, true_and
-/
lemma cauchy_iff_le {l : Filter α} [hl : l.NeBot] :
    Cauchy l ↔ l ×ˢ l <= 𝓤 α := by
  simp only [Cauchy, hl, true_and]

/--
theorem `Cauchy.ultrafilter_of` / 定理 `Cauchy.ultrafilter_of`

English:
theorem Cauchy.ultrafilter_of
  given: {l : Filter α} (h : Cauchy l)
  proof: by
  have := h.1
  have := Ultrafilter.of_le l
  exact ⟨Ultrafilter.neBot _, (Filter.prod_mono this this).trans h.2⟩

中文:
定理 Cauchy.ultrafilter_of
  条件: {l : Filter α} (h : Cauchy l)
  证明: by
  have := h.1
  have := Ultrafilter.of_le l
  exact ⟨Ultrafilter.neBot _, (Filter.prod_mono this this).trans h.2⟩

Depends on / 依赖: Filter, Filter.prod_mono, Ultrafilter, Ultrafilter.neBot, Ultrafilter.of_le, of_le, prod_mono
-/
theorem Cauchy.ultrafilter_of {l : Filter α} (h : Cauchy l) :
    Cauchy (@Ultrafilter.of _ l h.1 : Filter α) := by
  have := h.1
  have := Ultrafilter.of_le l
  exact ⟨Ultrafilter.neBot _, (Filter.prod_mono this this).trans h.2⟩

/--
theorem `cauchy_map_iff` / 定理 `cauchy_map_iff`

English:
theorem cauchy_map_iff
  given: {l : Filter β} {f : β -> α}
  proof: by
  rw [Cauchy]; rw [map_neBot_iff]; rw [prod_map_map_eq]; rw [Tendsto]

中文:
定理 cauchy_map_iff
  条件: {l : Filter β} {f : β -> α}
  证明: by
  rw [Cauchy]; rw [map_neBot_iff]; rw [prod_map_map_eq]; rw [Tendsto]

Depends on / 依赖: Cauchy, Tendsto, map_neBot_iff, prod_map_map_eq
-/
theorem cauchy_map_iff {l : Filter β} {f : β -> α} :
    Cauchy (l.map f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α) := by
  rw [Cauchy]; rw [map_neBot_iff]; rw [prod_map_map_eq]; rw [Tendsto]

/--
theorem `cauchy_map_iff'` / 定理 `cauchy_map_iff'`

English:
theorem cauchy_map_iff'
  given: {l : Filter β} [hl : NeBot l] {f : β -> α}
  proof: cauchy_map_iff.trans and_iff_right hl

中文:
定理 cauchy_map_iff'
  条件: {l : Filter β} [hl : NeBot l] {f : β -> α}
  证明: cauchy_map_iff.trans and_iff_right hl

Depends on / 依赖: and_iff_right, cauchy_map_iff, cauchy_map_iff.trans
-/
theorem cauchy_map_iff' {l : Filter β} [hl : NeBot l] {f : β -> α} :
    Cauchy (l.map f) ↔ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α) :=
cauchy_map_iff.trans and_iff_right hl

/--
theorem `Cauchy.mono` / 定理 `Cauchy.mono`

English:
theorem Cauchy.mono
  given: {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g <= f)
  statement: Cauchy g
  proof: ⟨hg, le_trans (Filter.prod_mono h_le h_le) h_c.right⟩

中文:
定理 Cauchy.mono
  条件: {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g <= f)
  结论: Cauchy g
  证明: ⟨hg, le_trans (Filter.prod_mono h_le h_le) h_c.right⟩

Depends on / 依赖: Filter, Filter.prod_mono, h_c.right, h_le, le_trans, prod_mono
-/
theorem Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g <= f) : Cauchy g :=
  ⟨hg, le_trans (Filter.prod_mono h_le h_le) h_c.right⟩

/--
theorem `Cauchy.mono'` / 定理 `Cauchy.mono'`

English:
theorem Cauchy.mono'
  given: {f g : Filter α} (h_c : Cauchy f) (_ : NeBot g) (h_le : g <= f)
  statement: Cauchy g
  proof: h_c.mono h_le

中文:
定理 Cauchy.mono'
  条件: {f g : Filter α} (h_c : Cauchy f) (_ : NeBot g) (h_le : g <= f)
  结论: Cauchy g
  证明: h_c.mono h_le

Depends on / 依赖: h_c.mono, h_le
-/
theorem Cauchy.mono' {f g : Filter α} (h_c : Cauchy f) (_ : NeBot g) (h_le : g <= f) : Cauchy g :=
  h_c.mono h_le

/--
theorem `cauchy_nhds` / 定理 `cauchy_nhds`

English:
theorem cauchy_nhds
  given: {a : α}
  statement: Cauchy (𝓝 a)
  proof: ⟨nhds_neBot, nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)⟩

中文:
定理 cauchy_nhds
  条件: {a : α}
  结论: Cauchy (𝓝 a)
  证明: ⟨nhds_neBot, nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)⟩

Depends on / 依赖: nhds_le_uniformity, nhds_neBot, nhds_prod_eq, nhds_prod_eq.symm.trans_le, trans_le
-/
theorem cauchy_nhds {a : α} : Cauchy (𝓝 a) :=
  ⟨nhds_neBot, nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)⟩

/--
theorem `cauchy_pure` / 定理 `cauchy_pure`

English:
theorem cauchy_pure
  given: {a : α}
  statement: Cauchy (pure a)
  proof: cauchy_nhds.mono (pure_le_nhds a)

中文:
定理 cauchy_pure
  条件: {a : α}
  结论: Cauchy (pure a)
  证明: cauchy_nhds.mono (pure_le_nhds a)

Depends on / 依赖: cauchy_nhds, cauchy_nhds.mono, pure_le_nhds
-/
theorem cauchy_pure {a : α} : Cauchy (pure a) :=
  cauchy_nhds.mono (pure_le_nhds a)

/--
theorem `Filter.Tendsto.cauchy_map` / 定理 `Filter.Tendsto.cauchy_map`

English:
theorem Filter.Tendsto.cauchy_map
  statement: {l : Filter β} [NeBot l] {f : β -> α} {a : α}
  proof: cauchy_nhds.mono h

中文:
定理 Filter.Tendsto.cauchy_map
  结论: {l : Filter β} [NeBot l] {f : β -> α} {a : α}
  证明: cauchy_nhds.mono h

Depends on / 依赖: cauchy_nhds, cauchy_nhds.mono
-/
theorem Filter.Tendsto.cauchy_map {l : Filter β} [NeBot l] {f : β -> α} {a : α}
    (h : Tendsto f l (𝓝 a)) : Cauchy (map f l) :=
  cauchy_nhds.mono h

/--
lemma `Cauchy.mono_uniformSpace` / 引理 `Cauchy.mono_uniformSpace`

English:
lemma Cauchy.mono_uniformSpace
  statement: {u v : UniformSpace β} {F : Filter β} (huv : u <= v)
  proof: ⟨hF.1, hF.2.trans huv⟩

中文:
引理 Cauchy.mono_uniformSpace
  结论: {u v : UniformSpace β} {F : Filter β} (huv : u <= v)
  证明: ⟨hF.1, hF.2.trans huv⟩

Depends on / 依赖: Cauchy, uniformSpace
-/
lemma Cauchy.mono_uniformSpace {u v : UniformSpace β} {F : Filter β} (huv : u <= v)
    (hF : Cauchy (uniformSpace := u) F) : Cauchy (uniformSpace := v) F :=
  ⟨hF.1, hF.2.trans huv⟩

/--
lemma `cauchy_inf_uniformSpace` / 引理 `cauchy_inf_uniformSpace`

English:
lemma cauchy_inf_uniformSpace
  given: {u v : UniformSpace β} {F : Filter β}
  proof: by
  unfold Cauchy
  rw [inf_uniformity (u := u)]; rw [le_inf_iff]; rw [and_and_left]

中文:
引理 cauchy_inf_uniformSpace
  条件: {u v : UniformSpace β} {F : Filter β}
  证明: by
  unfold Cauchy
  rw [inf_uniformity (u := u)]; rw [le_inf_iff]; rw [and_and_left]
-/
lemma cauchy_inf_uniformSpace {u v : UniformSpace β} {F : Filter β} :
    Cauchy (uniformSpace := u ⊓ v) F ↔
    Cauchy (uniformSpace := u) F ∧ Cauchy (uniformSpace := v) F := by
  unfold Cauchy
  rw [inf_uniformity (u := u)]; rw [le_inf_iff]; rw [and_and_left]

/--
lemma `cauchy_iInf_uniformSpace` / 引理 `cauchy_iInf_uniformSpace`

English:
lemma cauchy_iInf_uniformSpace
  statement: {ι : Sort*} [Nonempty ι] {u : ι -> UniformSpace β}
  proof: by
  unfold Cauchy
  rw [iInf_uniformity]; rw [le_iInf_iff]; rw [forall_and]; rw [forall_const]

中文:
引理 cauchy_iInf_uniformSpace
  结论: {ι : Sort*} [Nonempty ι] {u : ι -> UniformSpace β}
  证明: by
  unfold Cauchy
  rw [iInf_uniformity]; rw [le_iInf_iff]; rw [forall_and]; rw [forall_const]

Depends on / 依赖: Cauchy, forall_and, forall_const, iInf_uniformity, le_iInf_iff, uniformSpace
-/
lemma cauchy_iInf_uniformSpace {ι : Sort*} [Nonempty ι] {u : ι -> UniformSpace β}
    {l : Filter β} :
    Cauchy (uniformSpace := ⨅ i, u i) l ↔ forall i, Cauchy (uniformSpace := u i) l := by
  unfold Cauchy
  rw [iInf_uniformity]; rw [le_iInf_iff]; rw [forall_and]; rw [forall_const]

/--
lemma `cauchy_iInf_uniformSpace'` / 引理 `cauchy_iInf_uniformSpace'`

English:
lemma cauchy_iInf_uniformSpace'
  statement: {ι : Sort*} {u : ι -> UniformSpace β}
  proof: by
  simp_rw [cauchy_iff_le (uniformSpace := _), iInf_uniformity, le_iInf_iff]

中文:
引理 cauchy_iInf_uniformSpace'
  结论: {ι : Sort*} {u : ι -> UniformSpace β}
  证明: by
  simp_rw [cauchy_iff_le (uniformSpace := _), iInf_uniformity, le_iInf_iff]

Depends on / 依赖: Cauchy, cauchy_iff_le, iInf_uniformity, le_iInf_iff, simp_rw, uniformSpace
-/
lemma cauchy_iInf_uniformSpace' {ι : Sort*} {u : ι -> UniformSpace β}
    {l : Filter β} [l.NeBot] :
    Cauchy (uniformSpace := ⨅ i, u i) l ↔ forall i, Cauchy (uniformSpace := u i) l := by
  simp_rw [cauchy_iff_le (uniformSpace := _), iInf_uniformity, le_iInf_iff]

/--
lemma `cauchy_comap_uniformSpace` / 引理 `cauchy_comap_uniformSpace`

English:
lemma cauchy_comap_uniformSpace
  given: {u : UniformSpace β} {α} {f : α -> β} {l : Filter α}
  proof: by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap]
  rfl

中文:
引理 cauchy_comap_uniformSpace
  条件: {u : UniformSpace β} {α} {f : α -> β} {l : Filter α}
  证明: by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap]
  rfl

Depends on / 依赖: Cauchy, map_le_iff_le_comap, map_neBot_iff, prod_map_map_eq
-/
lemma cauchy_comap_uniformSpace {u : UniformSpace β} {α} {f : α -> β} {l : Filter α} :
    Cauchy (uniformSpace := comap f u) l ↔ Cauchy (map f l) := by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap]
  rfl

/--
lemma `cauchy_prod_iff` / 引理 `cauchy_prod_iff`

English:
lemma cauchy_prod_iff
  given: [UniformSpace β] {F : Filter (α × β)}
  proof: by
  simp_rw +instances [instUniformSpaceProd, ← cauchy_comap_uniformSpace, ← cauchy_inf_uniformSpace]

中文:
引理 cauchy_prod_iff
  条件: [UniformSpace β] {F : Filter (α × β)}
  证明: by
  simp_rw +instances [instUniformSpaceProd, ← cauchy_comap_uniformSpace, ← cauchy_inf_uniformSpace]

Depends on / 依赖: cauchy_comap_uniformSpace, cauchy_inf_uniformSpace, instUniformSpaceProd, instances, simp_rw
-/
lemma cauchy_prod_iff [UniformSpace β] {F : Filter (α × β)} :
    Cauchy F ↔ Cauchy (map Prod.fst F) ∧ Cauchy (map Prod.snd F) := by
  simp_rw +instances [instUniformSpaceProd, ← cauchy_comap_uniformSpace, ← cauchy_inf_uniformSpace]

/--
theorem `Cauchy.prod` / 定理 `Cauchy.prod`

English:
theorem Cauchy.prod
  given: [UniformSpace β] {f : Filter α} {g : Filter β} (hf : Cauchy f) (hg : Cauchy g)
  proof: by
  have := hf.1; have := hg.1
  simpa [cauchy_prod_iff, hf.1] using ⟨hf, hg⟩

中文:
定理 Cauchy.prod
  条件: [UniformSpace β] {f : Filter α} {g : Filter β} (hf : Cauchy f) (hg : Cauchy g)
  证明: by
  have := hf.1; have := hg.1
  simpa [cauchy_prod_iff, hf.1] using ⟨hf, hg⟩

Depends on / 依赖: cauchy_prod_iff
-/
theorem Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} (hf : Cauchy f) (hg : Cauchy g) :
    Cauchy (f ×ˢ g) := by
  have := hf.1; have := hg.1
  simpa [cauchy_prod_iff, hf.1] using ⟨hf, hg⟩

/--
theorem `le_nhds_of_cauchy_adhp_aux` / 定理 `le_nhds_of_cauchy_adhp_aux`

English:
theorem le_nhds_of_cauchy_adhp_aux
  statement: {f : Filter α} {x : α}
  proof: by
  -- Consider a neighborhood `s` of `x`
  intro s hs
  -- Take an entourage twice smaller than `s`
  rcases comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 hs) with ⟨U, U_mem, hU⟩
  -- Take a set `t ∈ f`, `t × t ⊆ U`, and a point `y ∈ t` such that `(x, y) ∈ U`
  rcases adhs U U_mem with

中文:
定理 le_nhds_of_cauchy_adhp_aux
  结论: {f : Filter α} {x : α}
  证明: by
  -- Consider a neighborhood `s` of `x`
  intro s hs
  -- Take an entourage twice smaller than `s`
  rcases comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 hs) with ⟨U, U_mem, hU⟩
  -- Take a set `t ∈ f`, `t × t ⊆ U`, and a point `y ∈ t` such that `(x, y) ∈ U`
  rcases adhs U U_mem with
-/
theorem le_nhds_of_cauchy_adhp_aux {f : Filter α} {x : α}
    (adhs : forall s in 𝓤 α, exists t in f, t ×ˢ t subseteq s ∧ exists y, (x, y) in s ∧ y in t) : f <= 𝓝 x := by
  -- Consider a neighborhood `s` of `x`
  intro s hs
  -- Take an entourage twice smaller than `s`
  rcases comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 hs) with ⟨U, U_mem, hU⟩
  -- Take a set `t ∈ f`, `t × t ⊆ U`, and a point `y ∈ t` such that `(x, y) ∈ U`
  rcases adhs U U_mem with ⟨t, t_mem, ht, y, hxy, hy⟩
  apply mem_of_superset t_mem
  -- Given a point `z ∈ t`, we have `(x, y) ∈ U` and `(y, z) ∈ t × t ⊆ U`, hence `z ∈ s`
  exact fun z hz => hU (SetRel.prodMk_mem_comp hxy (ht <| mk_mem_prod hy hz)) rfl

/--
theorem `le_nhds_of_cauchy_adhp` / 定理 `le_nhds_of_cauchy_adhp`

English:
theorem le_nhds_of_cauchy_adhp
  given: {f : Filter α} {x : α} (hf : Cauchy f) (adhs : ClusterPt x f)
  proof: le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      obtain ⟨t, t_mem, ht⟩ : exists t in f, t ×ˢ t subseteq s := (cauchy_iff.1 hf).2 s hs
      use t, t_mem, ht
      exact forall_mem_nonempty_iff_neBot.2 adhs _ (inter_mem_inf (mem_nhds_left x hs) t_mem))

中文:
定理 le_nhds_of_cauchy_adhp
  条件: {f : Filter α} {x : α} (hf : Cauchy f) (adhs : ClusterPt x f)
  证明: le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      obtain ⟨t, t_mem, ht⟩ : exists t in f, t ×ˢ t subseteq s := (cauchy_iff.1 hf).2 s hs
      use t, t_mem, ht
      exact forall_mem_nonempty_iff_neBot.2 adhs _ (inter_mem_inf (mem_nhds_left x hs) t_mem))

Depends on / 依赖: cauchy_iff, forall_mem_nonempty_iff_neBot, inter_mem_inf, le_nhds_of_cauchy_adhp_aux, mem_nhds_left, subseteq, t_mem
-/
theorem le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (hf : Cauchy f) (adhs : ClusterPt x f) :
    f <= 𝓝 x :=
  le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      obtain ⟨t, t_mem, ht⟩ : exists t in f, t ×ˢ t subseteq s := (cauchy_iff.1 hf).2 s hs
      use t, t_mem, ht
      exact forall_mem_nonempty_iff_neBot.2 adhs _ (inter_mem_inf (mem_nhds_left x hs) t_mem))

/--
theorem `le_nhds_iff_adhp_of_cauchy` / 定理 `le_nhds_iff_adhp_of_cauchy`

English:
theorem le_nhds_iff_adhp_of_cauchy
  given: {f : Filter α} {x : α} (hf : Cauchy f)
  proof: ⟨fun h => ClusterPt.of_le_nhds' h hf.1, le_nhds_of_cauchy_adhp hf⟩

中文:
定理 le_nhds_iff_adhp_of_cauchy
  条件: {f : Filter α} {x : α} (hf : Cauchy f)
  证明: ⟨fun h => ClusterPt.of_le_nhds' h hf.1, le_nhds_of_cauchy_adhp hf⟩

Depends on / 依赖: ClusterPt, ClusterPt.of_le_nhds, le_nhds_of_cauchy_adhp, of_le_nhds
-/
theorem le_nhds_iff_adhp_of_cauchy {f : Filter α} {x : α} (hf : Cauchy f) :
    f <= 𝓝 x ↔ ClusterPt x f :=
  ⟨fun h => ClusterPt.of_le_nhds' h hf.1, le_nhds_of_cauchy_adhp hf⟩

/--
theorem `Cauchy.map` / 定理 `Cauchy.map`

English:
theorem Cauchy.map
  statement: [UniformSpace β] {f : Filter α} {m : α -> β} (hf : Cauchy f)
  proof: ⟨hf.1.map _,
    calc
      map m f ×ˢ map m f = map (Prod.map m m) (f ×ˢ f) := Filter.prod_map_map_eq
      _ <= Filter.map (Prod.map m m) (𝓤 α) := map_mono hf.right
      _ <= 𝓤 β := hm⟩

中文:
定理 Cauchy.map
  结论: [UniformSpace β] {f : Filter α} {m : α -> β} (hf : Cauchy f)
  证明: ⟨hf.1.map _,
    calc
      map m f ×ˢ map m f = map (Prod.map m m) (f ×ˢ f) := Filter.prod_map_map_eq
      _ <= Filter.map (Prod.map m m) (𝓤 α) := map_mono hf.right
      _ <= 𝓤 β := hm⟩
-/
protected theorem Cauchy.map [UniformSpace β] {f : Filter α} {m : α -> β} (hf : Cauchy f)
    (hm : UniformContinuous m) : Cauchy (map m f) :=
  ⟨hf.1.map _,
    calc
      map m f ×ˢ map m f = map (Prod.map m m) (f ×ˢ f) := Filter.prod_map_map_eq
      _ <= Filter.map (Prod.map m m) (𝓤 α) := map_mono hf.right
      _ <= 𝓤 β := hm⟩

/--
theorem `Cauchy.comap` / 定理 `Cauchy.comap`

English:
theorem Cauchy.comap
  statement: [UniformSpace β] {f : Filter β} {m : α -> β} (hf : Cauchy f)
  proof: ⟨‹_›,
    calc
      comap m f ×ˢ comap m f = comap (Prod.map m m) (f ×ˢ f) := prod_comap_comap_eq
      _ <= comap (Prod.map m m) (𝓤 β) := comap_mono hf.right
      _ <= 𝓤 α := hm⟩

中文:
定理 Cauchy.comap
  结论: [UniformSpace β] {f : Filter β} {m : α -> β} (hf : Cauchy f)
  证明: ⟨‹_›,
    calc
      comap m f ×ˢ comap m f = comap (Prod.map m m) (f ×ˢ f) := prod_comap_comap_eq
      _ <= comap (Prod.map m m) (𝓤 β) := comap_mono hf.right
      _ <= 𝓤 α := hm⟩
-/
protected theorem Cauchy.comap [UniformSpace β] {f : Filter β} {m : α -> β} (hf : Cauchy f)
    (hm : comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) <= 𝓤 α) [NeBot (comap m f)] :
    Cauchy (comap m f) :=
  ⟨‹_›,
    calc
      comap m f ×ˢ comap m f = comap (Prod.map m m) (f ×ˢ f) := prod_comap_comap_eq
      _ <= comap (Prod.map m m) (𝓤 β) := comap_mono hf.right
      _ <= 𝓤 α := hm⟩

/--
theorem `Cauchy.comap'` / 定理 `Cauchy.comap'`

English:
theorem Cauchy.comap'
  statement: [UniformSpace β] {f : Filter β} {m : α -> β} (hf : Cauchy f)
  proof: hf.comap hm

中文:
定理 Cauchy.comap'
  结论: [UniformSpace β] {f : Filter β} {m : α -> β} (hf : Cauchy f)
  证明: hf.comap hm

Depends on / 依赖: hf.comap
-/
theorem Cauchy.comap' [UniformSpace β] {f : Filter β} {m : α -> β} (hf : Cauchy f)
    (hm : Filter.comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) <= 𝓤 α)
    (_ : NeBot (Filter.comap m f)) : Cauchy (Filter.comap m f) :=
  hf.comap hm

/--
lemma `Cauchy.map_of_le` / 引理 `Cauchy.map_of_le`

English:
lemma Cauchy.map_of_le
  statement: [UniformSpace β] {f : Filter α} {m : α -> β} (hf : Cauchy f) {s : Set α}
  proof: by
  suffices Cauchy (comap (Subtype.val : s -> α) f) by
    simpa [Set.domRestrict_def, ← Function.comp_def, ← map_map,
      subtype_coe_map_comap, inf_eq_left.mpr hfs] using this.map hm.restrict
  exact hf.comap' (fun _ x => x) (comap_coe_neBot_of_le_principal (h := hf.1) hfs)

中文:
引理 Cauchy.map_of_le
  结论: [UniformSpace β] {f : Filter α} {m : α -> β} (hf : Cauchy f) {s : Set α}
  证明: by
  suffices Cauchy (comap (Subtype.val : s -> α) f) by
    simpa [Set.domRestrict_def, ← Function.comp_def, ← map_map,
      subtype_coe_map_comap, inf_eq_left.mpr hfs] using this.map hm.restrict
  exact hf.comap' (fun _ x => x) (comap_coe_neBot_of_le_principal (h := hf.1) hfs)

Depends on / 依赖: Cauchy, Function, Function.comp_def, Set.domRestrict_def, Subtype, Subtype.val, comap_coe_neBot_of_le_principal, comp_def, domRestrict_def, hf.comap, hm.restrict, inf_eq_left, inf_eq_left.mpr, map_map, restrict, subtype_coe_map_comap, this.map
-/
lemma Cauchy.map_of_le [UniformSpace β] {f : Filter α} {m : α -> β} (hf : Cauchy f) {s : Set α}
    (hm : UniformContinuousOn m s) (hfs : f <= 𝓟 s) :
    Cauchy (map m f) := by
  suffices Cauchy (comap (Subtype.val : s -> α) f) by
    simpa [Set.domRestrict_def, ← Function.comp_def, ← map_map,
      subtype_coe_map_comap, inf_eq_left.mpr hfs] using this.map hm.restrict
  exact hf.comap' (fun _ x => x) (comap_coe_neBot_of_le_principal (h := hf.1) hfs)

/--
Definition of `CauchySeq` / `CauchySeq` 的定义

English:
definition CauchySeq
  signature: [Preorder β] (u : β -> α)
  body: Cauchy (atTop.map u)

中文:
定义 CauchySeq
  签名: [Preorder β] (u : β -> α)
  定义体: Cauchy (atTop.map u)

Depends on / 依赖: Cauchy, atTop.map
-/
def CauchySeq [Preorder β] (u : β -> α) :=
  Cauchy (atTop.map u)

/--
theorem `CauchySeq.tendsto_uniformity` / 定理 `CauchySeq.tendsto_uniformity`

English:
theorem CauchySeq.tendsto_uniformity
  given: [Preorder β] {u : β -> α} (h : CauchySeq u)
  proof: by
  simpa only [Tendsto, prod_map_map_eq', prod_atTop_atTop_eq] using h.right

中文:
定理 CauchySeq.tendsto_uniformity
  条件: [Preorder β] {u : β -> α} (h : CauchySeq u)
  证明: by
  simpa only [Tendsto, prod_map_map_eq', prod_atTop_atTop_eq] using h.right

Depends on / 依赖: Tendsto, h.right, prod_atTop_atTop_eq, prod_map_map_eq
-/
theorem CauchySeq.tendsto_uniformity [Preorder β] {u : β -> α} (h : CauchySeq u) :
    Tendsto (Prod.map u u) atTop (𝓤 α) := by
  simpa only [Tendsto, prod_map_map_eq', prod_atTop_atTop_eq] using h.right

/--
theorem `CauchySeq.nonempty` / 定理 `CauchySeq.nonempty`

English:
theorem CauchySeq.nonempty
  given: [Preorder β] {u : β -> α} (hu : CauchySeq u)
  statement: Nonempty β
  proof: @nonempty_of_neBot _ _ (map_neBot_iff _).1 hu.1

中文:
定理 CauchySeq.nonempty
  条件: [Preorder β] {u : β -> α} (hu : CauchySeq u)
  结论: Nonempty β
  证明: @nonempty_of_neBot _ _ (map_neBot_iff _).1 hu.1

Depends on / 依赖: map_neBot_iff, nonempty_of_neBot
-/
theorem CauchySeq.nonempty [Preorder β] {u : β -> α} (hu : CauchySeq u) : Nonempty β :=
@nonempty_of_neBot _ _ (map_neBot_iff _).1 hu.1

/--
theorem `CauchySeq.mem_entourage` / 定理 `CauchySeq.mem_entourage`

English:
theorem CauchySeq.mem_entourage
  statement: {β : Type*} [SemilatticeSup β] {u : β -> α} (h : CauchySeq u)
  proof: by
  have := h.nonempty
  have := h.tendsto_uniformity; rw [← prod_atTop_atTop_eq] at this
  simpa [MapsTo] using atTop_basis.prod_self.tendsto_left_iff.1 this V hV

中文:
定理 CauchySeq.mem_entourage
  结论: {β : 类型} [SemilatticeSup β] {u : β -> α} (h : CauchySeq u)
  证明: by
  have := h.nonempty
  have := h.tendsto_uniformity; rw [← prod_atTop_atTop_eq] at this
  simpa [MapsTo] using atTop_basis.prod_self.tendsto_left_iff.1 this V hV

Depends on / 依赖: MapsTo, atTop_basis, atTop_basis.prod_self.tendsto_left_iff, h.nonempty, h.tendsto_uniformity, nonempty, prod_atTop_atTop_eq, prod_self, tendsto_left_iff, tendsto_uniformity
-/
theorem CauchySeq.mem_entourage {β : Type*} [SemilatticeSup β] {u : β -> α} (h : CauchySeq u)
    {V : SetRel α α} (hV : V in 𝓤 α) : exists k₀, forall i j, k₀ <= i -> k₀ <= j -> (u i, u j) in V := by
  have := h.nonempty
  have := h.tendsto_uniformity; rw [← prod_atTop_atTop_eq] at this
  simpa [MapsTo] using atTop_basis.prod_self.tendsto_left_iff.1 this V hV

/--
theorem `Filter.Tendsto.cauchySeq` / 定理 `Filter.Tendsto.cauchySeq`

English:
theorem Filter.Tendsto.cauchySeq
  statement: [SemilatticeSup β] [Nonempty β] {f : β -> α} {x}
  proof: hx.cauchy_map

中文:
定理 Filter.Tendsto.cauchySeq
  结论: [SemilatticeSup β] [Nonempty β] {f : β -> α} {x}
  证明: hx.cauchy_map

Depends on / 依赖: cauchy_map, hx.cauchy_map
-/
theorem Filter.Tendsto.cauchySeq [SemilatticeSup β] [Nonempty β] {f : β -> α} {x}
    (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f :=
  hx.cauchy_map

/--
theorem `cauchySeq_const` / 定理 `cauchySeq_const`

English:
theorem cauchySeq_const
  given: [SemilatticeSup β] [Nonempty β] (x : α)
  statement: CauchySeq fun _ : β => x
  proof: tendsto_const_nhds.cauchySeq

中文:
定理 cauchySeq_const
  条件: [SemilatticeSup β] [Nonempty β] (x : α)
  结论: CauchySeq fun _ : β => x
  证明: tendsto_const_nhds.cauchySeq

Depends on / 依赖: cauchySeq, tendsto_const_nhds, tendsto_const_nhds.cauchySeq
-/
theorem cauchySeq_const [SemilatticeSup β] [Nonempty β] (x : α) : CauchySeq fun _ : β => x :=
  tendsto_const_nhds.cauchySeq

/--
theorem `cauchySeq_iff_tendsto` / 定理 `cauchySeq_iff_tendsto`

English:
theorem cauchySeq_iff_tendsto
  given: [Nonempty β] [SemilatticeSup β] {u : β -> α}
  proof: cauchy_map_iff'.trans by simp only [prod_atTop_atTop_eq, Prod.map_def]

中文:
定理 cauchySeq_iff_tendsto
  条件: [Nonempty β] [SemilatticeSup β] {u : β -> α}
  证明: cauchy_map_iff'.trans by simp only [prod_atTop_atTop_eq, Prod.map_def]

Depends on / 依赖: Prod.map_def, cauchy_map_iff, map_def, prod_atTop_atTop_eq
-/
theorem cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSup β] {u : β -> α} :
    CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α) :=
cauchy_map_iff'.trans by simp only [prod_atTop_atTop_eq, Prod.map_def]

/--
theorem `CauchySeq.comp_tendsto` / 定理 `CauchySeq.comp_tendsto`

English:
theorem CauchySeq.comp_tendsto
  statement: {γ} [Preorder β] [SemilatticeSup γ] [Nonempty γ] {f : β -> α}
  proof: ⟨inferInstance, le_trans (prod_le_prod.mpr ⟨Tendsto.comp le_rfl hg, Tendsto.comp le_rfl hg⟩) hf.2⟩

中文:
定理 CauchySeq.comp_tendsto
  结论: {γ} [Preorder β] [SemilatticeSup γ] [Nonempty γ] {f : β -> α}
  证明: ⟨inferInstance, le_trans (prod_le_prod.mpr ⟨Tendsto.comp le_rfl hg, Tendsto.comp le_rfl hg⟩) hf.2⟩

Depends on / 依赖: Tendsto, Tendsto.comp, le_rfl, le_trans, prod_le_prod, prod_le_prod.mpr
-/
theorem CauchySeq.comp_tendsto {γ} [Preorder β] [SemilatticeSup γ] [Nonempty γ] {f : β -> α}
    (hf : CauchySeq f) {g : γ -> β} (hg : Tendsto g atTop atTop) : CauchySeq (f ∘ g) :=
  ⟨inferInstance, le_trans (prod_le_prod.mpr ⟨Tendsto.comp le_rfl hg, Tendsto.comp le_rfl hg⟩) hf.2⟩

/--
theorem `CauchySeq.comp_injective` / 定理 `CauchySeq.comp_injective`

English:
theorem CauchySeq.comp_injective
  statement: [SemilatticeSup β] [NoMaxOrder β] [Nonempty β] {u : Nat -> α}
  proof: hu.comp_tendsto Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite.mono_left atTop_le_cofinite

中文:
定理 CauchySeq.comp_injective
  结论: [SemilatticeSup β] [NoMaxOrder β] [Nonempty β] {u : 自然数 -> α}
  证明: hu.comp_tendsto Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite.mono_left atTop_le_cofinite

Depends on / 依赖: Nat.cofinite_eq_atTop, atTop_le_cofinite, cofinite_eq_atTop, comp_tendsto, hf.tendsto_cofinite.mono_left, hu.comp_tendsto, mono_left, tendsto_cofinite
-/
theorem CauchySeq.comp_injective [SemilatticeSup β] [NoMaxOrder β] [Nonempty β] {u : Nat -> α}
    (hu : CauchySeq u) {f : β -> Nat} (hf : Injective f) : CauchySeq (u ∘ f) :=
hu.comp_tendsto Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite.mono_left atTop_le_cofinite

/--
theorem `Function.Bijective.cauchySeq_comp_iff` / 定理 `Function.Bijective.cauchySeq_comp_iff`

English:
theorem Function.Bijective.cauchySeq_comp_iff
  given: {f : Nat -> Nat} (hf : Bijective f) (u : Nat -> α)
  proof: by
  refine ⟨fun H => ?_, fun H => H.comp_injective hf.injective⟩
  lift f to Nat ≃ Nat using hf
  simpa only [Function.comp_def, f.apply_symm_apply] using H.comp_injective f.symm.injective

中文:
定理 Function.Bijective.cauchySeq_comp_iff
  条件: {f : 自然数 -> 自然数} (hf : Bijective f) (u : 自然数 -> α)
  证明: by
  refine ⟨fun H => ?_, fun H => H.comp_injective hf.injective⟩
  lift f to Nat ≃ Nat using hf
  simpa only [Function.comp_def, f.apply_symm_apply] using H.comp_injective f.symm.injective

Depends on / 依赖: Function, Function.comp_def, H.comp_injective, apply_symm_apply, comp_def, comp_injective, f.apply_symm_apply, f.symm.injective, hf.injective, injective
-/
theorem Function.Bijective.cauchySeq_comp_iff {f : Nat -> Nat} (hf : Bijective f) (u : Nat -> α) :
    CauchySeq (u ∘ f) ↔ CauchySeq u := by
  refine ⟨fun H => ?_, fun H => H.comp_injective hf.injective⟩
  lift f to Nat ≃ Nat using hf
  simpa only [Function.comp_def, f.apply_symm_apply] using H.comp_injective f.symm.injective

/--
theorem `CauchySeq.subseq_subseq_mem` / 定理 `CauchySeq.subseq_subseq_mem`

English:
theorem CauchySeq.subseq_subseq_mem
  statement: {V : Nat -> SetRel α α} (hV : forall n, V n in 𝓤 α) {u : Nat -> α}
  proof: by
  rw [cauchySeq_iff_tendsto] at hu
  exact ((hu.comp <| hf.prod_atTop hg).comp tendsto_atTop_diagonal).subseq_mem hV

中文:
定理 CauchySeq.subseq_subseq_mem
  结论: {V : 自然数 -> SetRel α α} (hV : 对任意 n, V n in 𝓤 α) {u : 自然数 -> α}
  证明: by
  rw [cauchySeq_iff_tendsto] at hu
  exact ((hu.comp <| hf.prod_atTop hg).comp tendsto_atTop_diagonal).subseq_mem hV

Depends on / 依赖: cauchySeq_iff_tendsto, hf.prod_atTop, hu.comp, prod_atTop, subseq_mem, tendsto_atTop_diagonal
-/
theorem CauchySeq.subseq_subseq_mem {V : Nat -> SetRel α α} (hV : forall n, V n in 𝓤 α) {u : Nat -> α}
    (hu : CauchySeq u) {f g : Nat -> Nat} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    exists φ : Nat -> Nat, StrictMono φ ∧ forall n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) in V n := by
  rw [cauchySeq_iff_tendsto] at hu
  exact ((hu.comp <| hf.prod_atTop hg).comp tendsto_atTop_diagonal).subseq_mem hV

-- todo: generalize this and other lemmas to a nonempty semilattice
/--
theorem `cauchySeq_iff'` / 定理 `cauchySeq_iff'`

English:
theorem cauchySeq_iff'
  given: {u : Nat -> α}
  proof: cauchySeq_iff_tendsto

中文:
定理 cauchySeq_iff'
  条件: {u : 自然数 -> α}
  证明: cauchySeq_iff_tendsto

Depends on / 依赖: cauchySeq_iff_tendsto
-/
theorem cauchySeq_iff' {u : Nat -> α} :
    CauchySeq u ↔ forall V in 𝓤 α, forallᶠ k in atTop, k in Prod.map u u ⁻¹' V :=
  cauchySeq_iff_tendsto

/--
theorem `cauchySeq_iff` / 定理 `cauchySeq_iff`

English:
theorem cauchySeq_iff
  given: {u : Nat -> α}
  proof: by
  simp only [cauchySeq_iff', Filter.eventually_atTop_prod_self', mem_preimage, Prod.map_apply]

中文:
定理 cauchySeq_iff
  条件: {u : 自然数 -> α}
  证明: by
  simp only [cauchySeq_iff', Filter.eventually_atTop_prod_self', mem_preimage, Prod.map_apply]

Depends on / 依赖: Filter, Filter.eventually_atTop_prod_self, Prod.map_apply, cauchySeq_iff, eventually_atTop_prod_self, map_apply, mem_preimage
-/
theorem cauchySeq_iff {u : Nat -> α} :
    CauchySeq u ↔ forall V in 𝓤 α, exists N, forall k >= N, forall l >= N, (u k, u l) in V := by
  simp only [cauchySeq_iff', Filter.eventually_atTop_prod_self', mem_preimage, Prod.map_apply]

/--
theorem `CauchySeq.prodMap` / 定理 `CauchySeq.prodMap`

English:
theorem CauchySeq.prodMap
  statement: {γ δ} [UniformSpace β] [Preorder γ] [Preorder δ] {u : γ -> α} {v : δ -> β}
  proof: by
  simpa only [CauchySeq, prod_map_map_eq', prod_atTop_atTop_eq] using hu.prod hv

中文:
定理 CauchySeq.prodMap
  结论: {γ δ} [UniformSpace β] [Preorder γ] [Preorder δ] {u : γ -> α} {v : δ -> β}
  证明: by
  simpa only [CauchySeq, prod_map_map_eq', prod_atTop_atTop_eq] using hu.prod hv

Depends on / 依赖: CauchySeq, hu.prod, prod_atTop_atTop_eq, prod_map_map_eq
-/
theorem CauchySeq.prodMap {γ δ} [UniformSpace β] [Preorder γ] [Preorder δ] {u : γ -> α} {v : δ -> β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq (Prod.map u v) := by
  simpa only [CauchySeq, prod_map_map_eq', prod_atTop_atTop_eq] using hu.prod hv

/--
theorem `CauchySeq.prodMk` / 定理 `CauchySeq.prodMk`

English:
theorem CauchySeq.prodMk
  statement: {γ} [UniformSpace β] [Preorder γ] {u : γ -> α} {v : γ -> β}
  proof: haveI := hu.1.of_map
  (Cauchy.prod hu hv).mono (tendsto_map.prodMk tendsto_map)

中文:
定理 CauchySeq.prodMk
  结论: {γ} [UniformSpace β] [Preorder γ] {u : γ -> α} {v : γ -> β}
  证明: haveI := hu.1.of_map
  (Cauchy.prod hu hv).mono (tendsto_map.prodMk tendsto_map)

Depends on / 依赖: Cauchy, Cauchy.prod, of_map, prodMk, tendsto_map, tendsto_map.prodMk
-/
theorem CauchySeq.prodMk {γ} [UniformSpace β] [Preorder γ] {u : γ -> α} {v : γ -> β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq fun x => (u x, v x) :=
  haveI := hu.1.of_map
  (Cauchy.prod hu hv).mono (tendsto_map.prodMk tendsto_map)

/--
theorem `CauchySeq.eventually_eventually` / 定理 `CauchySeq.eventually_eventually`

English:
theorem CauchySeq.eventually_eventually
  statement: [Preorder β] {u : β -> α} (hu : CauchySeq u)
  proof: eventually_atTop_curry hu.tendsto_uniformity hV

中文:
定理 CauchySeq.eventually_eventually
  结论: [Preorder β] {u : β -> α} (hu : CauchySeq u)
  证明: eventually_atTop_curry hu.tendsto_uniformity hV

Depends on / 依赖: eventually_atTop_curry, hu.tendsto_uniformity, tendsto_uniformity
-/
theorem CauchySeq.eventually_eventually [Preorder β] {u : β -> α} (hu : CauchySeq u)
    {V : SetRel α α} (hV : V in 𝓤 α) : forallᶠ k in atTop, forallᶠ l in atTop, (u k, u l) in V :=
eventually_atTop_curry hu.tendsto_uniformity hV

/--
theorem `UniformContinuous.comp_cauchySeq` / 定理 `UniformContinuous.comp_cauchySeq`

English:
theorem UniformContinuous.comp_cauchySeq
  statement: {γ} [UniformSpace β] [Preorder γ] {f : α -> β}
  proof: hu.map hf

中文:
定理 UniformContinuous.comp_cauchySeq
  结论: {γ} [UniformSpace β] [Preorder γ] {f : α -> β}
  证明: hu.map hf

Depends on / 依赖: hu.map
-/
theorem UniformContinuous.comp_cauchySeq {γ} [UniformSpace β] [Preorder γ] {f : α -> β}
    (hf : UniformContinuous f) {u : γ -> α} (hu : CauchySeq u) : CauchySeq (f ∘ u) :=
  hu.map hf

/--
theorem `CauchySeq.subseq_mem` / 定理 `CauchySeq.subseq_mem`

English:
theorem CauchySeq.subseq_mem
  statement: {V : Nat -> SetRel α α} (hV : forall n, V n in 𝓤 α) {u : Nat -> α}
  proof: by
  have : forall n, exists N, forall k >= N, forall l >= k, (u l, u k) in V n := fun n => by
    rw [cauchySeq_iff] at hu
    rcases hu _ (hV n) with ⟨N, H⟩
    exact ⟨N, fun k hk l hl => H _ (le_trans hk hl) _ hk⟩
  obtain ⟨φ : Nat -> Nat, φ_extr : StrictMono φ, hφ : forall n, forall l >= φ n, (u

中文:
定理 CauchySeq.subseq_mem
  结论: {V : 自然数 -> SetRel α α} (hV : 对任意 n, V n in 𝓤 α) {u : 自然数 -> α}
  证明: by
  have : forall n, exists N, forall k >= N, forall l >= k, (u l, u k) in V n := fun n => by
    rw [cauchySeq_iff] at hu
    rcases hu _ (hV n) with ⟨N, H⟩
    exact ⟨N, fun k hk l hl => H _ (le_trans hk hl) _ hk⟩
  obtain ⟨φ : Nat -> Nat, φ_extr : StrictMono φ, hφ : forall n, forall l >= φ n, (u

Depends on / 依赖: Nat.lt_add_one, StrictMono, cauchySeq_iff, extraction_forall_of_eventually, le_trans, lt_add_one
-/
theorem CauchySeq.subseq_mem {V : Nat -> SetRel α α} (hV : forall n, V n in 𝓤 α) {u : Nat -> α}
    (hu : CauchySeq u) : exists φ : Nat -> Nat, StrictMono φ ∧ forall n, (u <| φ (n + 1), u <| φ n) in V n := by
  have : forall n, exists N, forall k >= N, forall l >= k, (u l, u k) in V n := fun n => by
    rw [cauchySeq_iff] at hu
    rcases hu _ (hV n) with ⟨N, H⟩
    exact ⟨N, fun k hk l hl => H _ (le_trans hk hl) _ hk⟩
  obtain ⟨φ : Nat -> Nat, φ_extr : StrictMono φ, hφ : forall n, forall l >= φ n, (u l, u <| φ n) in V n⟩ :=
    extraction_forall_of_eventually' this
  exact ⟨φ, φ_extr, fun n => hφ _ _ (φ_extr <| Nat.lt_add_one n).le⟩

/--
theorem `Filter.Tendsto.subseq_mem_entourage` / 定理 `Filter.Tendsto.subseq_mem_entourage`

English:
theorem Filter.Tendsto.subseq_mem_entourage
  statement: {V : Nat -> SetRel α α} (hV : forall n, V n in 𝓤 α) {u : Nat -> α}
  proof: by
  rcases mem_atTop_sets.1 (hu (ball_mem_nhds a (symm_le_uniformity <| hV 0))) with ⟨n, hn⟩
  rcases (hu.comp (tendsto_add_atTop_nat n)).cauchySeq.subseq_mem fun n => hV (n + 1) with
    ⟨φ, φ_mono, hφV⟩
  exact ⟨fun k => φ k + n, φ_mono.add_const _, hn _ le_add_self, hφV⟩

中文:
定理 Filter.Tendsto.subseq_mem_entourage
  结论: {V : 自然数 -> SetRel α α} (hV : 对任意 n, V n in 𝓤 α) {u : 自然数 -> α}
  证明: by
  rcases mem_atTop_sets.1 (hu (ball_mem_nhds a (symm_le_uniformity <| hV 0))) with ⟨n, hn⟩
  rcases (hu.comp (tendsto_add_atTop_nat n)).cauchySeq.subseq_mem fun n => hV (n + 1) with
    ⟨φ, φ_mono, hφV⟩
  exact ⟨fun k => φ k + n, φ_mono.add_const _, hn _ le_add_self, hφV⟩

Depends on / 依赖: _mono.add_const, add_const, ball_mem_nhds, cauchySeq, cauchySeq.subseq_mem, hu.comp, le_add_self, mem_atTop_sets, subseq_mem, symm_le_uniformity, tendsto_add_atTop_nat
-/
theorem Filter.Tendsto.subseq_mem_entourage {V : Nat -> SetRel α α} (hV : forall n, V n in 𝓤 α) {u : Nat -> α}
    {a : α} (hu : Tendsto u atTop (𝓝 a)) : exists φ : Nat -> Nat, StrictMono φ ∧ (u (φ 0), a) in V 0 ∧
      forall n, (u <| φ (n + 1), u <| φ n) in V (n + 1) := by
  rcases mem_atTop_sets.1 (hu (ball_mem_nhds a (symm_le_uniformity <| hV 0))) with ⟨n, hn⟩
  rcases (hu.comp (tendsto_add_atTop_nat n)).cauchySeq.subseq_mem fun n => hV (n + 1) with
    ⟨φ, φ_mono, hφV⟩
  exact ⟨fun k => φ k + n, φ_mono.add_const _, hn _ le_add_self, hφV⟩

/--
theorem `tendsto_nhds_of_cauchySeq_of_subseq` / 定理 `tendsto_nhds_of_cauchySeq_of_subseq`

English:
theorem tendsto_nhds_of_cauchySeq_of_subseq
  statement: [Preorder β] {u : β -> α} (hu : CauchySeq u)
  proof: le_nhds_of_cauchy_adhp hu (ha.mapClusterPt.of_comp hf)

中文:
定理 tendsto_nhds_of_cauchySeq_of_subseq
  结论: [Preorder β] {u : β -> α} (hu : CauchySeq u)
  证明: le_nhds_of_cauchy_adhp hu (ha.mapClusterPt.of_comp hf)

Depends on / 依赖: ha.mapClusterPt.of_comp, le_nhds_of_cauchy_adhp, mapClusterPt, of_comp
-/
theorem tendsto_nhds_of_cauchySeq_of_subseq [Preorder β] {u : β -> α} (hu : CauchySeq u)
    {ι : Type*} {f : ι -> β} {p : Filter ι} [NeBot p] (hf : Tendsto f p atTop) {a : α}
    (ha : Tendsto (u ∘ f) p (𝓝 a)) : Tendsto u atTop (𝓝 a) :=
  le_nhds_of_cauchy_adhp hu (ha.mapClusterPt.of_comp hf)

/--
theorem `cauchySeq_shift` / 定理 `cauchySeq_shift`

English:
theorem cauchySeq_shift
  given: {u : Nat -> α} (k : Nat)
  statement: CauchySeq (fun n => u (n + k)) ↔ CauchySeq u
  proof: by
  constructor <;> intro h
  · rw [cauchySeq_iff] at h ⊢
    intro V mV
    obtain ⟨N, h⟩ := h V mV
    use N + k
    intro a ha b hb
    convert! h (a - k) (Nat.le_sub_of_add_le ha) (b - k) (Nat.le_sub_of_add_le hb) <;> lia
  · exact h.comp_tendsto (tendsto_add_atTop_nat k)

中文:
定理 cauchySeq_shift
  条件: {u : 自然数 -> α} (k : 自然数)
  结论: CauchySeq (fun n => u (n + k)) ↔ CauchySeq u
  证明: by
  constructor <;> intro h
  · rw [cauchySeq_iff] at h ⊢
    intro V mV
    obtain ⟨N, h⟩ := h V mV
    use N + k
    intro a ha b hb
    convert! h (a - k) (Nat.le_sub_of_add_le ha) (b - k) (Nat.le_sub_of_add_le hb) <;> lia
  · exact h.comp_tendsto (tendsto_add_atTop_nat k)

Depends on / 依赖: Nat.le_sub_of_add_le, cauchySeq_iff, comp_tendsto, convert, h.comp_tendsto, le_sub_of_add_le, tendsto_add_atTop_nat
-/
theorem cauchySeq_shift {u : Nat -> α} (k : Nat) : CauchySeq (fun n => u (n + k)) ↔ CauchySeq u := by
  constructor <;> intro h
  · rw [cauchySeq_iff] at h ⊢
    intro V mV
    obtain ⟨N, h⟩ := h V mV
    use N + k
    intro a ha b hb
    convert! h (a - k) (Nat.le_sub_of_add_le ha) (b - k) (Nat.le_sub_of_add_le hb) <;> lia
  · exact h.comp_tendsto (tendsto_add_atTop_nat k)

/--
theorem `Filter.HasBasis.cauchySeq_iff` / 定理 `Filter.HasBasis.cauchySeq_iff`

English:
theorem Filter.HasBasis.cauchySeq_iff
  statement: {γ} [Nonempty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop}
  proof: by
  rw [cauchySeq_iff_tendsto]; rw [← prod_atTop_atTop_eq]
  refine (atTop_basis.prod_self.tendsto_iff h).trans ?_
  simp only [true_and, Prod.forall, mem_prod_eq,
    mem_Ici, and_imp, Prod.map, @forall_comm (_ <= _) β]

中文:
定理 Filter.HasBasis.cauchySeq_iff
  结论: {γ} [Nonempty β] [SemilatticeSup β] {u : β -> α} {p : γ -> 命题}
  证明: by
  rw [cauchySeq_iff_tendsto]; rw [← prod_atTop_atTop_eq]
  refine (atTop_basis.prod_self.tendsto_iff h).trans ?_
  simp only [true_and, Prod.forall, mem_prod_eq,
    mem_Ici, and_imp, Prod.map, @forall_comm (_ <= _) β]

Depends on / 依赖: Prod.forall, Prod.map, and_imp, atTop_basis, atTop_basis.prod_self.tendsto_iff, cauchySeq_iff_tendsto, forall_comm, mem_Ici, mem_prod_eq, prod_atTop_atTop_eq, prod_self, tendsto_iff, true_and
-/
theorem Filter.HasBasis.cauchySeq_iff {γ} [Nonempty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop}
    {s : γ -> SetRel α α} (h : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ forall i, p i -> exists N, forall m, N <= m -> forall n, N <= n -> (u m, u n) in s i := by
  rw [cauchySeq_iff_tendsto]; rw [← prod_atTop_atTop_eq]
  refine (atTop_basis.prod_self.tendsto_iff h).trans ?_
  simp only [true_and, Prod.forall, mem_prod_eq,
    mem_Ici, and_imp, Prod.map, @forall_comm (_ <= _) β]

/--
theorem `Filter.HasBasis.cauchySeq_iff'` / 定理 `Filter.HasBasis.cauchySeq_iff'`

English:
theorem Filter.HasBasis.cauchySeq_iff'
  statement: {γ} [Nonempty β] [SemilatticeSup β] {u : β -> α}
  proof: by
  refine H.cauchySeq_iff.trans ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · exact (h i hi).imp fun N hN n hn => hN n hn N le_rfl
  · rcases comp_symm_of_uniformity (H.mem_of_mem hi) with ⟨t, ht, ht', hts⟩
    rcases H.mem_iff.1 ht with ⟨j, hj, hjt⟩
refine (h j hj).imp fun N hN m hm n hn => hts ⟨u N, 

中文:
定理 Filter.HasBasis.cauchySeq_iff'
  结论: {γ} [Nonempty β] [SemilatticeSup β] {u : β -> α}
  证明: by
  refine H.cauchySeq_iff.trans ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · exact (h i hi).imp fun N hN n hn => hN n hn N le_rfl
  · rcases comp_symm_of_uniformity (H.mem_of_mem hi) with ⟨t, ht, ht', hts⟩
    rcases H.mem_iff.1 ht with ⟨j, hj, hjt⟩
refine (h j hj).imp fun N hN m hm n hn => hts ⟨u N, 

Depends on / 依赖: H.cauchySeq_iff.trans, H.mem_iff, H.mem_of_mem, cauchySeq_iff, comp_symm_of_uniformity, exacts, le_rfl, mem_iff, mem_of_mem
-/
theorem Filter.HasBasis.cauchySeq_iff' {γ} [Nonempty β] [SemilatticeSup β] {u : β -> α}
    {p : γ -> Prop} {s : γ -> SetRel α α} (H : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ forall i, p i -> exists N, forall n >= N, (u n, u N) in s i := by
  refine H.cauchySeq_iff.trans ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · exact (h i hi).imp fun N hN n hn => hN n hn N le_rfl
  · rcases comp_symm_of_uniformity (H.mem_of_mem hi) with ⟨t, ht, ht', hts⟩
    rcases H.mem_iff.1 ht with ⟨j, hj, hjt⟩
refine (h j hj).imp fun N hN m hm n hn => hts ⟨u N, hjt ?_, ht' hjt ?_⟩
    exacts [hN m hm, hN n hn]

/--
theorem `cauchySeq_of_controlled` / 定理 `cauchySeq_of_controlled`

English:
theorem cauchySeq_of_controlled
  statement: [SemilatticeSup β] [Nonempty β] (U : β -> SetRel α α)
  proof: cauchySeq_iff_tendsto.2
    (by
      intro s hs
      rw [mem_map]; rw [mem_atTop_sets]
      obtain ⟨N, hN⟩ := hU s hs
      refine ⟨(N, N), fun mn hmn => ?_⟩
      obtain ⟨m, n⟩ := mn
      exact hN (hf hmn.1 hmn.2))

中文:
定理 cauchySeq_of_controlled
  结论: [SemilatticeSup β] [Nonempty β] (U : β -> SetRel α α)
  证明: cauchySeq_iff_tendsto.2
    (by
      intro s hs
      rw [mem_map]; rw [mem_atTop_sets]
      obtain ⟨N, hN⟩ := hU s hs
      refine ⟨(N, N), fun mn hmn => ?_⟩
      obtain ⟨m, n⟩ := mn
      exact hN (hf hmn.1 hmn.2))

Depends on / 依赖: cauchySeq_iff_tendsto, mem_atTop_sets, mem_map
-/
theorem cauchySeq_of_controlled [SemilatticeSup β] [Nonempty β] (U : β -> SetRel α α)
    (hU : forall s in 𝓤 α, exists n, U n subseteq s) {f : β -> α}
    (hf : forall ⦃N m n : β⦄, N <= m -> N <= n -> (f m, f n) in U N) : CauchySeq f :=
  cauchySeq_iff_tendsto.2
    (by
      intro s hs
      rw [mem_map]; rw [mem_atTop_sets]
      obtain ⟨N, hN⟩ := hU s hs
      refine ⟨(N, N), fun mn hmn => ?_⟩
      obtain ⟨m, n⟩ := mn
      exact hN (hf hmn.1 hmn.2))

/--
theorem `isComplete_iff_clusterPt` / 定理 `isComplete_iff_clusterPt`

English:
theorem isComplete_iff_clusterPt
  given: {s : Set α}
  proof: forall₃_congr fun _ hl _ => exists_congr fun _ => and_congr_right fun _ =>
    le_nhds_iff_adhp_of_cauchy hl

中文:
定理 isComplete_iff_clusterPt
  条件: {s : Set α}
  证明: forall₃_congr fun _ hl _ => exists_congr fun _ => and_congr_right fun _ =>
    le_nhds_iff_adhp_of_cauchy hl

Depends on / 依赖: and_congr_right, exists_congr, le_nhds_iff_adhp_of_cauchy
-/
theorem isComplete_iff_clusterPt {s : Set α} :
    IsComplete s ↔ forall l, Cauchy l -> l <= 𝓟 s -> exists x in s, ClusterPt x l :=
  forall₃_congr fun _ hl _ => exists_congr fun _ => and_congr_right fun _ =>
    le_nhds_iff_adhp_of_cauchy hl

/--
theorem `isComplete_iff_ultrafilter` / 定理 `isComplete_iff_ultrafilter`

English:
theorem isComplete_iff_ultrafilter
  given: {s : Set α}
  proof: by
  refine ⟨fun h l => h l, fun H => isComplete_iff_clusterPt.2 fun l hl hls => ?_⟩
  have := hl.1
  rcases H (Ultrafilter.of l) hl.ultrafilter_of ((Ultrafilter.of_le l).trans hls) with ⟨x, hxs, hxl⟩
  exact ⟨x, hxs, (ClusterPt.of_le_nhds hxl).mono (Ultrafilter.of_le l)⟩

中文:
定理 isComplete_iff_ultrafilter
  条件: {s : Set α}
  证明: by
  refine ⟨fun h l => h l, fun H => isComplete_iff_clusterPt.2 fun l hl hls => ?_⟩
  have := hl.1
  rcases H (Ultrafilter.of l) hl.ultrafilter_of ((Ultrafilter.of_le l).trans hls) with ⟨x, hxs, hxl⟩
  exact ⟨x, hxs, (ClusterPt.of_le_nhds hxl).mono (Ultrafilter.of_le l)⟩

Depends on / 依赖: ClusterPt, ClusterPt.of_le_nhds, Ultrafilter, Ultrafilter.of, Ultrafilter.of_le, hl.ultrafilter_of, isComplete_iff_clusterPt, of_le, of_le_nhds, ultrafilter_of
-/
theorem isComplete_iff_ultrafilter {s : Set α} :
    IsComplete s ↔ forall l : Ultrafilter α, Cauchy (l : Filter α) -> ↑l <= 𝓟 s -> exists x in s, ↑l <= 𝓝 x := by
  refine ⟨fun h l => h l, fun H => isComplete_iff_clusterPt.2 fun l hl hls => ?_⟩
  have := hl.1
  rcases H (Ultrafilter.of l) hl.ultrafilter_of ((Ultrafilter.of_le l).trans hls) with ⟨x, hxs, hxl⟩
  exact ⟨x, hxs, (ClusterPt.of_le_nhds hxl).mono (Ultrafilter.of_le l)⟩

/--
theorem `isComplete_iff_ultrafilter'` / 定理 `isComplete_iff_ultrafilter'`

English:
theorem isComplete_iff_ultrafilter'
  given: {s : Set α}
  proof: isComplete_iff_ultrafilter.trans by simp only [le_principal_iff, Ultrafilter.mem_coe]

中文:
定理 isComplete_iff_ultrafilter'
  条件: {s : Set α}
  证明: isComplete_iff_ultrafilter.trans by simp only [le_principal_iff, Ultrafilter.mem_coe]

Depends on / 依赖: Ultrafilter, Ultrafilter.mem_coe, isComplete_iff_ultrafilter, isComplete_iff_ultrafilter.trans, le_principal_iff, mem_coe
-/
theorem isComplete_iff_ultrafilter' {s : Set α} :
    IsComplete s ↔ forall l : Ultrafilter α, Cauchy (l : Filter α) -> s in l -> exists x in s, ↑l <= 𝓝 x :=
isComplete_iff_ultrafilter.trans by simp only [le_principal_iff, Ultrafilter.mem_coe]

/--
theorem `IsComplete.union` / 定理 `IsComplete.union`

English:
theorem IsComplete.union
  given: {s t : Set α} (hs : IsComplete s) (ht : IsComplete t)
  proof: by
  simp only [isComplete_iff_ultrafilter', Ultrafilter.union_mem_iff, or_imp] at *
  exact fun l hl =>
    ⟨fun hsl => (hs l hl hsl).imp fun x hx => ⟨Or.inl hx.1, hx.2⟩, fun htl =>
      (ht l hl htl).imp fun x hx => ⟨Or.inr hx.1, hx.2⟩⟩

中文:
定理 IsComplete.union
  条件: {s t : Set α} (hs : IsComplete s) (ht : IsComplete t)
  证明: by
  simp only [isComplete_iff_ultrafilter', Ultrafilter.union_mem_iff, or_imp] at *
  exact fun l hl =>
    ⟨fun hsl => (hs l hl hsl).imp fun x hx => ⟨Or.inl hx.1, hx.2⟩, fun htl =>
      (ht l hl htl).imp fun x hx => ⟨Or.inr hx.1, hx.2⟩⟩
-/
protected theorem IsComplete.union {s t : Set α} (hs : IsComplete s) (ht : IsComplete t) :
    IsComplete (s union t) := by
  simp only [isComplete_iff_ultrafilter', Ultrafilter.union_mem_iff, or_imp] at *
  exact fun l hl =>
    ⟨fun hsl => (hs l hl hsl).imp fun x hx => ⟨Or.inl hx.1, hx.2⟩, fun htl =>
      (ht l hl htl).imp fun x hx => ⟨Or.inr hx.1, hx.2⟩⟩

/--
theorem `isComplete_iUnion_separated` / 定理 `isComplete_iUnion_separated`

English:
theorem isComplete_iUnion_separated
  statement: {ι : Sort*} {s : ι -> Set α} (hs : forall i, IsComplete (s i))
  proof: by
  set S := ⋃ i, s i
  intro l hl hls
  rw [le_principal_iff] at hls
  obtain ⟨hl_ne, hl'⟩ := cauchy_iff.1 hl
  obtain ⟨t, htS, htl, htU⟩ : exists t, t subseteq S ∧ t in l ∧ t ×ˢ t subseteq U := by
    rcases hl' U hU with ⟨t, htl, htU⟩
    refine ⟨t inter S, inter_subset_right, inter_mem htl hls,

中文:
定理 isComplete_iUnion_separated
  结论: {ι : Sort*} {s : ι -> Set α} (hs : 对任意 i, IsComplete (s i))
  证明: by
  set S := ⋃ i, s i
  intro l hl hls
  rw [le_principal_iff] at hls
  obtain ⟨hl_ne, hl'⟩ := cauchy_iff.1 hl
  obtain ⟨t, htS, htl, htU⟩ : exists t, t subseteq S ∧ t in l ∧ t ×ˢ t subseteq U := by
    rcases hl' U hU with ⟨t, htl, htU⟩
    refine ⟨t inter S, inter_subset_right, inter_mem htl hls,

Depends on / 依赖: Filter, Filter.nonempty_of_mem, Subset, Subset.trans, cauchy_iff, hl_ne, inter_mem, inter_subset_left, inter_subset_right, le_principal_iff, mem_iUnion, nonempty_of_mem, subseteq
-/
theorem isComplete_iUnion_separated {ι : Sort*} {s : ι -> Set α} (hs : forall i, IsComplete (s i))
    {U : SetRel α α} (hU : U in 𝓤 α) (hd : forall (i j : ι), forall x in s i, forall y in s j, (x, y) in U -> i = j) :
    IsComplete (⋃ i, s i) := by
  set S := ⋃ i, s i
  intro l hl hls
  rw [le_principal_iff] at hls
  obtain ⟨hl_ne, hl'⟩ := cauchy_iff.1 hl
  obtain ⟨t, htS, htl, htU⟩ : exists t, t subseteq S ∧ t in l ∧ t ×ˢ t subseteq U := by
    rcases hl' U hU with ⟨t, htl, htU⟩
    refine ⟨t inter S, inter_subset_right, inter_mem htl hls, Subset.trans ?_ htU⟩
    gcongr <;> apply inter_subset_left
  obtain ⟨i, hi⟩ : exists i, t subseteq s i := by
    rcases Filter.nonempty_of_mem htl with ⟨x, hx⟩
    rcases mem_iUnion.1 (htS hx) with ⟨i, hi⟩
    refine ⟨i, fun y hy => ?_⟩
    rcases mem_iUnion.1 (htS hy) with ⟨j, hj⟩
    rwa [hd i j x hi y hj (htU <| mk_mem_prod hx hy)]
  rcases hs i l hl (le_principal_iff.2 <| mem_of_superset htl hi) with ⟨x, hxs, hlx⟩
  exact ⟨x, mem_iUnion.2 ⟨i, hxs⟩, hlx⟩

/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
@[wikidata Q848569]
/--
Definition of `CompleteSpace` / `CompleteSpace` 的定义

English:
class CompleteSpace
  parameters: (α : Type u) [UniformSpace α]
  axioms and operations (1):
    - complete : forall {f : Filter α}, Cauchy f -> exists x, f <= 𝓝 x

中文:
类 CompleteSpace
  参数: (α : 类型u) [UniformSpace α]
  公理与运算 (1 个):
    - complete : 对任意 {f : Filter α}, Cauchy f -> 存在 x, f <= 𝓝 x
-/
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete : forall {f : Filter α}, Cauchy f -> exists x, f <= 𝓝 x

/--
theorem `isComplete_univ` / 定理 `isComplete_univ`

English:
theorem isComplete_univ
  given: {α : Type u} [UniformSpace α] [CompleteSpace α]
  proof: fun f hf _ => by
  rcases CompleteSpace.complete hf with ⟨x, hx⟩
  exact ⟨x, mem_univ x, hx⟩

@[deprecated (since := "2026-07-27")] alias complete_univ := isComplete_univ

中文:
定理 isComplete_univ
  条件: {α : 类型u} [UniformSpace α] [CompleteSpace α]
  证明: fun f hf _ => by
  rcases CompleteSpace.complete hf with ⟨x, hx⟩
  exact ⟨x, mem_univ x, hx⟩

@[deprecated (since := "2026-07-27")] alias complete_univ := isComplete_univ

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, complete, mem_univ
-/
theorem isComplete_univ {α : Type u} [UniformSpace α] [CompleteSpace α] :
    IsComplete (univ : Set α) := fun f hf _ => by
  rcases CompleteSpace.complete hf with ⟨x, hx⟩
  exact ⟨x, mem_univ x, hx⟩

@[deprecated (since := "2026-07-27")] alias complete_univ := isComplete_univ

/--
Instance `CompleteSpace.prod` / 实例 `CompleteSpace.prod`

English:
instance CompleteSpace.prod
  signature: [UniformSpace β] [CompleteSpace α] [CompleteSpace β]
  body: let ⟨x1, hx1⟩ := CompleteSpace.complete hf.map uniformContinuous_fst
let ⟨x2, hx2⟩ := CompleteSpace.complete hf.map uniformContinuous_snd
    ⟨(x1, x2), by rw [nhds_prod_eq, le_prod]; constructor <;> assumption⟩

中文:
实例 CompleteSpace.prod
  签名: [UniformSpace β] [CompleteSpace α] [CompleteSpace β]
  定义体: let ⟨x1, hx1⟩ := CompleteSpace.complete hf.map uniformContinuous_fst
let ⟨x2, hx2⟩ := CompleteSpace.complete hf.map uniformContinuous_snd
    ⟨(x1, x2), by rw [nhds_prod_eq, le_prod]; constructor <;> assumption⟩

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, complete, hf.map, le_prod, nhds_prod_eq, uniformContinuous_fst, uniformContinuous_snd
-/
instance CompleteSpace.prod [UniformSpace β] [CompleteSpace α] [CompleteSpace β] :
    CompleteSpace (α × β) where
  complete hf :=
let ⟨x1, hx1⟩ := CompleteSpace.complete hf.map uniformContinuous_fst
let ⟨x2, hx2⟩ := CompleteSpace.complete hf.map uniformContinuous_snd
    ⟨(x1, x2), by rw [nhds_prod_eq, le_prod]; constructor <;> assumption⟩

/--
lemma `CompleteSpace.fst_of_prod` / 引理 `CompleteSpace.fst_of_prod`

English:
lemma CompleteSpace.fst_of_prod
  given: [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty β]
  proof: let ⟨y⟩ := h
let ⟨(a, b), hab⟩ := CompleteSpace.complete hf.prod cauchy_pure (a := y)
    ⟨a, by simpa only [map_fst_prod, nhds_prod_eq] using map_mono (m := Prod.fst) hab⟩

中文:
引理 CompleteSpace.fst_of_prod
  条件: [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty β]
  证明: let ⟨y⟩ := h
let ⟨(a, b), hab⟩ := CompleteSpace.complete hf.prod cauchy_pure (a := y)
    ⟨a, by simpa only [map_fst_prod, nhds_prod_eq] using map_mono (m := Prod.fst) hab⟩

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, Prod.fst, cauchy_pure, complete, hf.prod, map_fst_prod, map_mono, nhds_prod_eq
-/
lemma CompleteSpace.fst_of_prod [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty β] :
    CompleteSpace α where
  complete hf :=
    let ⟨y⟩ := h
let ⟨(a, b), hab⟩ := CompleteSpace.complete hf.prod cauchy_pure (a := y)
    ⟨a, by simpa only [map_fst_prod, nhds_prod_eq] using map_mono (m := Prod.fst) hab⟩

/--
lemma `CompleteSpace.snd_of_prod` / 引理 `CompleteSpace.snd_of_prod`

English:
lemma CompleteSpace.snd_of_prod
  given: [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty α]
  proof: let ⟨x⟩ := h
let ⟨(a, b), hab⟩ := CompleteSpace.complete (cauchy_pure (a := x)).prod hf
    ⟨b, by simpa only [map_snd_prod, nhds_prod_eq] using map_mono (m := Prod.snd) hab⟩

中文:
引理 CompleteSpace.snd_of_prod
  条件: [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty α]
  证明: let ⟨x⟩ := h
let ⟨(a, b), hab⟩ := CompleteSpace.complete (cauchy_pure (a := x)).prod hf
    ⟨b, by simpa only [map_snd_prod, nhds_prod_eq] using map_mono (m := Prod.snd) hab⟩

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, Prod.snd, cauchy_pure, complete, map_mono, map_snd_prod, nhds_prod_eq
-/
lemma CompleteSpace.snd_of_prod [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty α] :
    CompleteSpace β where
  complete hf :=
    let ⟨x⟩ := h
let ⟨(a, b), hab⟩ := CompleteSpace.complete (cauchy_pure (a := x)).prod hf
    ⟨b, by simpa only [map_snd_prod, nhds_prod_eq] using map_mono (m := Prod.snd) hab⟩

/--
lemma `completeSpace_prod_of_nonempty` / 引理 `completeSpace_prod_of_nonempty`

English:
lemma completeSpace_prod_of_nonempty
  given: [UniformSpace β] [Nonempty α] [Nonempty β]
  proof: ⟨fun _ => ⟨.fst_of_prod (β := β), .snd_of_prod (α := α)⟩, fun ⟨_, _⟩ => .prod⟩

@[to_additive]

中文:
引理 completeSpace_prod_of_nonempty
  条件: [UniformSpace β] [Nonempty α] [Nonempty β]
  证明: ⟨fun _ => ⟨.fst_of_prod (β := β), .snd_of_prod (α := α)⟩, fun ⟨_, _⟩ => .prod⟩

@[to_additive]

Depends on / 依赖: fst_of_prod, snd_of_prod
-/
lemma completeSpace_prod_of_nonempty [UniformSpace β] [Nonempty α] [Nonempty β] :
    CompleteSpace (α × β) ↔ CompleteSpace α ∧ CompleteSpace β :=
  ⟨fun _ => ⟨.fst_of_prod (β := β), .snd_of_prod (α := α)⟩, fun ⟨_, _⟩ => .prod⟩

@[to_additive]
/--
Instance `CompleteSpace.mulOpposite` / 实例 `CompleteSpace.mulOpposite`

English:
instance CompleteSpace.mulOpposite
  signature: [CompleteSpace α]
  body: MulOpposite.op_surjective.exists.mpr
      let ⟨x, hx⟩ := CompleteSpace.complete (hf.map MulOpposite.uniformContinuous_unop)
⟨x, (map_le_iff_le_comap.mp hx).trans_eq MulOpposite.comap_unop_nhds _⟩

中文:
实例 CompleteSpace.mulOpposite
  签名: [CompleteSpace α]
  定义体: MulOpposite.op_surjective.exists.mpr
      let ⟨x, hx⟩ := CompleteSpace.complete (hf.map MulOpposite.uniformContinuous_unop)
⟨x, (map_le_iff_le_comap.mp hx).trans_eq MulOpposite.comap_unop_nhds _⟩

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, MulOpposite, MulOpposite.comap_unop_nhds, MulOpposite.op_surjective.exists.mpr, MulOpposite.uniformContinuous_unop, comap_unop_nhds, complete, hf.map, map_le_iff_le_comap, map_le_iff_le_comap.mp, op_surjective, trans_eq, uniformContinuous_unop
-/
instance CompleteSpace.mulOpposite [CompleteSpace α] : CompleteSpace αᵐᵒᵖ where
  complete hf :=
MulOpposite.op_surjective.exists.mpr
      let ⟨x, hx⟩ := CompleteSpace.complete (hf.map MulOpposite.uniformContinuous_unop)
⟨x, (map_le_iff_le_comap.mp hx).trans_eq MulOpposite.comap_unop_nhds _⟩

/--
theorem `completeSpace_of_isComplete_univ` / 定理 `completeSpace_of_isComplete_univ`

English:
theorem completeSpace_of_isComplete_univ
  given: (h : IsComplete (univ : Set α))
  statement: CompleteSpace α
  proof: ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩

中文:
定理 completeSpace_of_isComplete_univ
  条件: (h : IsComplete (univ : Set α))
  结论: CompleteSpace α
  证明: ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩

Depends on / 依赖: le_top, principal_univ
-/
theorem completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : CompleteSpace α :=
  ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩

/--
theorem `completeSpace_iff_isComplete_univ` / 定理 `completeSpace_iff_isComplete_univ`

English:
theorem completeSpace_iff_isComplete_univ
  statement: CompleteSpace α ↔ IsComplete (univ : Set α)
  proof: ⟨@isComplete_univ α _, completeSpace_of_isComplete_univ⟩

中文:
定理 completeSpace_iff_isComplete_univ
  结论: CompleteSpace α ↔ IsComplete (univ : Set α)
  证明: ⟨@isComplete_univ α _, completeSpace_of_isComplete_univ⟩

Depends on / 依赖: completeSpace_of_isComplete_univ, isComplete_univ
-/
theorem completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : Set α) :=
  ⟨@isComplete_univ α _, completeSpace_of_isComplete_univ⟩

/--
theorem `completeSpace_iff_ultrafilter` / 定理 `completeSpace_iff_ultrafilter`

English:
theorem completeSpace_iff_ultrafilter
  proof: by
  simp [completeSpace_iff_isComplete_univ, isComplete_iff_ultrafilter]

中文:
定理 completeSpace_iff_ultrafilter
  证明: by
  simp [completeSpace_iff_isComplete_univ, isComplete_iff_ultrafilter]

Depends on / 依赖: completeSpace_iff_isComplete_univ, isComplete_iff_ultrafilter
-/
theorem completeSpace_iff_ultrafilter :
    CompleteSpace α ↔ forall l : Ultrafilter α, Cauchy (l : Filter α) -> exists x : α, ↑l <= 𝓝 x := by
  simp [completeSpace_iff_isComplete_univ, isComplete_iff_ultrafilter]

/--
theorem `cauchy_iff_exists_le_nhds` / 定理 `cauchy_iff_exists_le_nhds`

English:
theorem cauchy_iff_exists_le_nhds
  given: [CompleteSpace α] {l : Filter α} [NeBot l]
  proof: ⟨CompleteSpace.complete, fun ⟨_, hx⟩ => cauchy_nhds.mono hx⟩

中文:
定理 cauchy_iff_exists_le_nhds
  条件: [CompleteSpace α] {l : Filter α} [NeBot l]
  证明: ⟨CompleteSpace.complete, fun ⟨_, hx⟩ => cauchy_nhds.mono hx⟩

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, cauchy_nhds, cauchy_nhds.mono, complete
-/
theorem cauchy_iff_exists_le_nhds [CompleteSpace α] {l : Filter α} [NeBot l] :
    Cauchy l ↔ exists x, l <= 𝓝 x :=
  ⟨CompleteSpace.complete, fun ⟨_, hx⟩ => cauchy_nhds.mono hx⟩

/--
theorem `cauchy_map_iff_exists_tendsto` / 定理 `cauchy_map_iff_exists_tendsto`

English:
theorem cauchy_map_iff_exists_tendsto
  given: [CompleteSpace α] {l : Filter β} {f : β -> α} [NeBot l]
  proof: cauchy_iff_exists_le_nhds

中文:
定理 cauchy_map_iff_exists_tendsto
  条件: [CompleteSpace α] {l : Filter β} {f : β -> α} [NeBot l]
  证明: cauchy_iff_exists_le_nhds

Depends on / 依赖: cauchy_iff_exists_le_nhds
-/
theorem cauchy_map_iff_exists_tendsto [CompleteSpace α] {l : Filter β} {f : β -> α} [NeBot l] :
    Cauchy (l.map f) ↔ exists x, Tendsto f l (𝓝 x) :=
  cauchy_iff_exists_le_nhds

/--
theorem `cauchySeq_tendsto_of_complete` / 定理 `cauchySeq_tendsto_of_complete`

English:
theorem cauchySeq_tendsto_of_complete
  statement: [Preorder β] [CompleteSpace α] {u : β -> α}
  proof: CompleteSpace.complete H

中文:
定理 cauchySeq_tendsto_of_complete
  结论: [Preorder β] [CompleteSpace α] {u : β -> α}
  证明: CompleteSpace.complete H

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, complete
-/
theorem cauchySeq_tendsto_of_complete [Preorder β] [CompleteSpace α] {u : β -> α}
    (H : CauchySeq u) : exists x, Tendsto u atTop (𝓝 x) :=
  CompleteSpace.complete H

/--
theorem `cauchySeq_tendsto_of_isComplete` / 定理 `cauchySeq_tendsto_of_isComplete`

English:
theorem cauchySeq_tendsto_of_isComplete
  statement: [Preorder β] {K : Set α} (h₁ : IsComplete K)
  proof: h₁ _ h₃ le_principal_iff.2 mem_map_iff_exists_image.2
    ⟨univ, univ_mem, by rwa [image_univ, range_subset_iff]⟩

中文:
定理 cauchySeq_tendsto_of_isComplete
  结论: [Preorder β] {K : Set α} (h₁ : IsComplete K)
  证明: h₁ _ h₃ le_principal_iff.2 mem_map_iff_exists_image.2
    ⟨univ, univ_mem, by rwa [image_univ, range_subset_iff]⟩

Depends on / 依赖: image_univ, le_principal_iff, mem_map_iff_exists_image, range_subset_iff, univ_mem
-/
theorem cauchySeq_tendsto_of_isComplete [Preorder β] {K : Set α} (h₁ : IsComplete K)
    {u : β -> α} (h₂ : forall n, u n in K) (h₃ : CauchySeq u) : exists v in K, Tendsto u atTop (𝓝 v) :=
h₁ _ h₃ le_principal_iff.2 mem_map_iff_exists_image.2
    ⟨univ, univ_mem, by rwa [image_univ, range_subset_iff]⟩

/--
theorem `Cauchy.le_nhds_lim` / 定理 `Cauchy.le_nhds_lim`

English:
theorem Cauchy.le_nhds_lim
  given: [CompleteSpace α] {f : Filter α} (hf : Cauchy f)
  proof: hf.1.nonempty; f <= 𝓝 (lim f) :=
  _root_.le_nhds_lim (CompleteSpace.complete hf)

中文:
定理 Cauchy.le_nhds_lim
  条件: [CompleteSpace α] {f : Filter α} (hf : Cauchy f)
  证明: hf.1.nonempty; f <= 𝓝 (lim f) :=
  _root_.le_nhds_lim (CompleteSpace.complete hf)

Depends on / 依赖: nonempty
-/
theorem Cauchy.le_nhds_lim [CompleteSpace α] {f : Filter α} (hf : Cauchy f) :
    haveI := hf.1.nonempty; f <= 𝓝 (lim f) :=
  _root_.le_nhds_lim (CompleteSpace.complete hf)

/--
theorem `CauchySeq.tendsto_limUnder` / 定理 `CauchySeq.tendsto_limUnder`

English:
theorem CauchySeq.tendsto_limUnder
  given: [Preorder β] [CompleteSpace α] {u : β -> α} (h : CauchySeq u)
  proof: h.1.nonempty; Tendsto u atTop (𝓝 <| limUnder atTop u) :=
  h.le_nhds_lim

中文:
定理 CauchySeq.tendsto_limUnder
  条件: [Preorder β] [CompleteSpace α] {u : β -> α} (h : CauchySeq u)
  证明: h.1.nonempty; Tendsto u atTop (𝓝 <| limUnder atTop u) :=
  h.le_nhds_lim

Depends on / 依赖: Tendsto, limUnder, nonempty
-/
theorem CauchySeq.tendsto_limUnder [Preorder β] [CompleteSpace α] {u : β -> α} (h : CauchySeq u) :
    haveI := h.1.nonempty; Tendsto u atTop (𝓝 <| limUnder atTop u) :=
  h.le_nhds_lim

/--
theorem `IsClosed.isComplete` / 定理 `IsClosed.isComplete`

English:
theorem IsClosed.isComplete
  given: [CompleteSpace α] {s : Set α} (h : IsClosed s)
  statement: IsComplete s
  proof: fun _ cf fs =>
  let ⟨x, hx⟩ := CompleteSpace.complete cf
  ⟨x, isClosed_iff_clusterPt.mp h x (cf.left.mono (le_inf hx fs)), hx⟩

中文:
定理 IsClosed.isComplete
  条件: [CompleteSpace α] {s : Set α} (h : IsClosed s)
  结论: IsComplete s
  证明: fun _ cf fs =>
  let ⟨x, hx⟩ := CompleteSpace.complete cf
  ⟨x, isClosed_iff_clusterPt.mp h x (cf.left.mono (le_inf hx fs)), hx⟩

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, cf.left.mono, complete, isClosed_iff_clusterPt, isClosed_iff_clusterPt.mp, le_inf
-/
theorem IsClosed.isComplete [CompleteSpace α] {s : Set α} (h : IsClosed s) : IsComplete s :=
  fun _ cf fs =>
  let ⟨x, hx⟩ := CompleteSpace.complete cf
  ⟨x, isClosed_iff_clusterPt.mp h x (cf.left.mono (le_inf hx fs)), hx⟩

namespace DiscreteUniformity

variable [DiscreteUniformity α]

/--
theorem `eq_pure_of_cauchy` / 定理 `eq_pure_of_cauchy`

English:
theorem eq_pure_of_cauchy
  given: {f : Filter α} (hf : Cauchy f)
  statement: exists x : α, f = pure x
  proof: by
  rcases hf with ⟨f_ne_bot, f_le⟩
  simp only [DiscreteUniformity.eq_principal_setRelId, le_principal_iff, mem_prod_iff] at f_le
  obtain ⟨S, hS, T, hT, H⟩ := f_le
  obtain ⟨x, rfl, _, _, _⟩ := SetRel.exists_eq_singleton_of_prod_subset_id
    (f_ne_bot.nonempty_of_mem hS) (f_ne_bot.nonempty_of_me

中文:
定理 eq_pure_of_cauchy
  条件: {f : Filter α} (hf : Cauchy f)
  结论: 存在 x : α, f = pure x
  证明: by
  rcases hf with ⟨f_ne_bot, f_le⟩
  simp only [DiscreteUniformity.eq_principal_setRelId, le_principal_iff, mem_prod_iff] at f_le
  obtain ⟨S, hS, T, hT, H⟩ := f_le
  obtain ⟨x, rfl, _, _, _⟩ := SetRel.exists_eq_singleton_of_prod_subset_id
    (f_ne_bot.nonempty_of_mem hS) (f_ne_bot.nonempty_of_me

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.eq_principal_setRelId, SetRel, SetRel.exists_eq_singleton_of_prod_subset_id, eq_principal_setRelId, exists_eq_singleton_of_prod_subset_id, f_le, f_ne_bot, f_ne_bot.le_pure_iff.mp, f_ne_bot.nonempty_of_mem, le_principal_iff, le_pure_iff, le_pure_iff.mpr, mem_prod_iff, nonempty_of_mem
-/
theorem eq_pure_of_cauchy {f : Filter α} (hf : Cauchy f) : exists x : α, f = pure x := by
  rcases hf with ⟨f_ne_bot, f_le⟩
  simp only [DiscreteUniformity.eq_principal_setRelId, le_principal_iff, mem_prod_iff] at f_le
  obtain ⟨S, hS, T, hT, H⟩ := f_le
  obtain ⟨x, rfl, _, _, _⟩ := SetRel.exists_eq_singleton_of_prod_subset_id
    (f_ne_bot.nonempty_of_mem hS) (f_ne_bot.nonempty_of_mem hT) H
exact ⟨x, f_ne_bot.le_pure_iff.mp le_pure_iff.mpr hS⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace α
  body: by
    obtain ⟨x, rfl⟩ := eq_pure_of_cauchy hf
    exact ⟨x, pure_le_nhds x⟩

中文:
实例 :
  签名: CompleteSpace α
  定义体: by
    obtain ⟨x, rfl⟩ := eq_pure_of_cauchy hf
    exact ⟨x, pure_le_nhds x⟩

Depends on / 依赖: eq_pure_of_cauchy, pure_le_nhds
-/
instance : CompleteSpace α where
  complete {f} hf := by
    obtain ⟨x, rfl⟩ := eq_pure_of_cauchy hf
    exact ⟨x, pure_le_nhds x⟩

variable {X}

/--
Definition of `cauchyConst` / `cauchyConst` 的定义

English:
definition cauchyConst
  signature: {f : Filter α} (hf : Cauchy f)
  body: (eq_pure_of_cauchy hf).choose

中文:
定义 cauchyConst
  签名: {f : Filter α} (hf : Cauchy f)
  定义体: (eq_pure_of_cauchy hf).choose

Depends on / 依赖: eq_pure_of_cauchy
-/
noncomputable def cauchyConst {f : Filter α} (hf : Cauchy f) : α :=
  (eq_pure_of_cauchy hf).choose

/--
theorem `eq_pure_cauchyConst` / 定理 `eq_pure_cauchyConst`

English:
theorem eq_pure_cauchyConst
  given: {f : Filter α} (hf : Cauchy f)
  statement: f = pure (cauchyConst hf)
  proof: (eq_pure_of_cauchy hf).choose_spec

中文:
定理 eq_pure_cauchyConst
  条件: {f : Filter α} (hf : Cauchy f)
  结论: f = pure (cauchyConst hf)
  证明: (eq_pure_of_cauchy hf).choose_spec

Depends on / 依赖: choose_spec, eq_pure_of_cauchy
-/
theorem eq_pure_cauchyConst {f : Filter α} (hf : Cauchy f) : f = pure (cauchyConst hf) :=
  (eq_pure_of_cauchy hf).choose_spec

end DiscreteUniformity

/--
Definition of `TotallyBounded` / `TotallyBounded` 的定义

English:
definition TotallyBounded
  signature: (s : Set α)
  body: forall d in 𝓤 α, exists t : Set α, t.Finite ∧ s subseteq ⋃ y in t, { x | (x, y) in d }

中文:
定义 TotallyBounded
  签名: (s : Set α)
  定义体: forall d in 𝓤 α, exists t : Set α, t.Finite ∧ s subseteq ⋃ y in t, { x | (x, y) in d }

Depends on / 依赖: Finite, subseteq, t.Finite
-/
def TotallyBounded (s : Set α) : Prop :=
  forall d in 𝓤 α, exists t : Set α, t.Finite ∧ s subseteq ⋃ y in t, { x | (x, y) in d }

/--
Definition of `Filter.TotallyBounded` / `Filter.TotallyBounded` 的定义

English:
definition Filter.TotallyBounded
  signature: (f : Filter α)
  body: forall d : SetRel α α, d in 𝓤 α -> exists t : Set α, t.Finite ∧ d.preimage t in f

中文:
定义 Filter.TotallyBounded
  签名: (f : Filter α)
  定义体: forall d : SetRel α α, d in 𝓤 α -> exists t : Set α, t.Finite ∧ d.preimage t in f
-/
protected def Filter.TotallyBounded (f : Filter α) :=
  forall d : SetRel α α, d in 𝓤 α -> exists t : Set α, t.Finite ∧ d.preimage t in f

/--
theorem `Filter.totallyBounded_principal_iff` / 定理 `Filter.totallyBounded_principal_iff`

English:
theorem Filter.totallyBounded_principal_iff
  given: {s : Set α}
  proof: by
  simp only [Filter.TotallyBounded, mem_principal, SetRel.preimage_eq_biUnion, TotallyBounded]

中文:
定理 Filter.totallyBounded_principal_iff
  条件: {s : Set α}
  证明: by
  simp only [Filter.TotallyBounded, mem_principal, SetRel.preimage_eq_biUnion, TotallyBounded]

Depends on / 依赖: Filter, Filter.TotallyBounded, SetRel, SetRel.preimage_eq_biUnion, TotallyBounded, mem_principal, preimage_eq_biUnion
-/
theorem Filter.totallyBounded_principal_iff {s : Set α} :
    (𝓟 s).TotallyBounded ↔ TotallyBounded s := by
  simp only [Filter.TotallyBounded, mem_principal, SetRel.preimage_eq_biUnion, TotallyBounded]

/--
theorem `Filter.TotallyBounded.exists_subset_of_mem` / 定理 `Filter.TotallyBounded.exists_subset_of_mem`

English:
theorem Filter.TotallyBounded.exists_subset_of_mem
  statement: {f : Filter α} (hf : f.TotallyBounded)
  proof: by
  rcases comp_symm_of_uniformity hU with ⟨r, hr, rs, rU⟩
  rcases hf r hr with ⟨k, fk, ks⟩
  let u := k inter { y | exists x in s, (x, y) in r }
  choose g hgs hgr using fun x : u => x.coe_prop.2
  refine ⟨range g, ?_, ?_, ?_⟩
  · exact range_subset_iff.2 hgs
  · have : Fintype u := (fk.inter_of_

中文:
定理 Filter.TotallyBounded.exists_subset_of_mem
  结论: {f : Filter α} (hf : f.TotallyBounded)
  证明: by
  rcases comp_symm_of_uniformity hU with ⟨r, hr, rs, rU⟩
  rcases hf r hr with ⟨k, fk, ks⟩
  let u := k inter { y | exists x in s, (x, y) in r }
  choose g hgs hgr using fun x : u => x.coe_prop.2
  refine ⟨range g, ?_, ?_, ?_⟩
  · exact range_subset_iff.2 hgs
  · have : Fintype u := (fk.inter_of_

Depends on / 依赖: Fintype, SetRel, SetRel.preimage, coe_prop, comp_symm_of_uniformity, exists_range_iff, filter_upwards, finite_range, fintype, fk.inter_of_left, inter_of_left, preimage, range_subset_iff, simp_rw, x.coe_prop
-/
theorem Filter.TotallyBounded.exists_subset_of_mem {f : Filter α} (hf : f.TotallyBounded)
    {s : Set α} (hs : s in f) {U : SetRel α α} (hU : U in 𝓤 α) :
    exists t subseteq s, Set.Finite t ∧ U.preimage t in f := by
  rcases comp_symm_of_uniformity hU with ⟨r, hr, rs, rU⟩
  rcases hf r hr with ⟨k, fk, ks⟩
  let u := k inter { y | exists x in s, (x, y) in r }
  choose g hgs hgr using fun x : u => x.coe_prop.2
  refine ⟨range g, ?_, ?_, ?_⟩
  · exact range_subset_iff.2 hgs
  · have : Fintype u := (fk.inter_of_left _).fintype
    exact finite_range g
  · filter_upwards [hs, ks] with x xs ⟨y, hy, xy⟩
    simp_rw [SetRel.preimage, exists_range_iff]
    set z : ↥u := ⟨y, hy, ⟨x, xs, xy⟩⟩
    exact ⟨z, rU ⟨y, xy, rs (hgr z)⟩⟩

/--
theorem `TotallyBounded.exists_subset` / 定理 `TotallyBounded.exists_subset`

English:
theorem TotallyBounded.exists_subset
  statement: {s : Set α} (hs : TotallyBounded s) {U : SetRel α α}
  proof: by
  rw [← Filter.totallyBounded_principal_iff] at hs
  simp_rw [← SetRel.preimage_eq_biUnion]
  exact hs.exists_subset_of_mem (Filter.mem_principal_self s) hU

中文:
定理 TotallyBounded.exists_subset
  结论: {s : Set α} (hs : TotallyBounded s) {U : SetRel α α}
  证明: by
  rw [← Filter.totallyBounded_principal_iff] at hs
  simp_rw [← SetRel.preimage_eq_biUnion]
  exact hs.exists_subset_of_mem (Filter.mem_principal_self s) hU

Depends on / 依赖: Filter, Filter.mem_principal_self, Filter.totallyBounded_principal_iff, SetRel, SetRel.preimage_eq_biUnion, exists_subset_of_mem, hs.exists_subset_of_mem, mem_principal_self, preimage_eq_biUnion, simp_rw, totallyBounded_principal_iff
-/
theorem TotallyBounded.exists_subset {s : Set α} (hs : TotallyBounded s) {U : SetRel α α}
    (hU : U in 𝓤 α) : exists t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y in t, { x | (x, y) in U } := by
  rw [← Filter.totallyBounded_principal_iff] at hs
  simp_rw [← SetRel.preimage_eq_biUnion]
  exact hs.exists_subset_of_mem (Filter.mem_principal_self s) hU

/--
theorem `totallyBounded_iff_subset` / 定理 `totallyBounded_iff_subset`

English:
theorem totallyBounded_iff_subset
  given: {s : Set α}
  proof: ⟨fun H _ hd => H.exists_subset hd, fun H d hd => let ⟨t, _, ht⟩ := H d hd; ⟨t, ht⟩⟩

中文:
定理 totallyBounded_iff_subset
  条件: {s : Set α}
  证明: ⟨fun H _ hd => H.exists_subset hd, fun H d hd => let ⟨t, _, ht⟩ := H d hd; ⟨t, ht⟩⟩

Depends on / 依赖: H.exists_subset, exists_subset
-/
theorem totallyBounded_iff_subset {s : Set α} :
    TotallyBounded s ↔
      forall d in 𝓤 α, exists t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y in t, { x | (x, y) in d } :=
  ⟨fun H _ hd => H.exists_subset hd, fun H d hd => let ⟨t, _, ht⟩ := H d hd; ⟨t, ht⟩⟩

/--
theorem `Filter.HasBasis.totallyBounded_iff` / 定理 `Filter.HasBasis.totallyBounded_iff`

English:
theorem Filter.HasBasis.totallyBounded_iff
  statement: {ι} {p : ι -> Prop} {U : ι -> SetRel α α}
  proof: H.forall_iff fun _ _ hUV h =>
h.imp fun _ ht => ⟨ht.1, ht.2.trans iUnion₂_mono fun _ _ _ hy => hUV hy⟩

中文:
定理 Filter.HasBasis.totallyBounded_iff
  结论: {ι} {p : ι -> 命题} {U : ι -> SetRel α α}
  证明: H.forall_iff fun _ _ hUV h =>
h.imp fun _ ht => ⟨ht.1, ht.2.trans iUnion₂_mono fun _ _ _ hy => hUV hy⟩

Depends on / 依赖: H.forall_iff, forall_iff, h.imp
-/
theorem Filter.HasBasis.totallyBounded_iff {ι} {p : ι -> Prop} {U : ι -> SetRel α α}
    (H : (𝓤 α).HasBasis p U) {s : Set α} :
    TotallyBounded s ↔ forall i, p i -> exists t : Set α, Set.Finite t ∧ s subseteq ⋃ y in t, { x | (x, y) in U i } :=
  H.forall_iff fun _ _ hUV h =>
h.imp fun _ ht => ⟨ht.1, ht.2.trans iUnion₂_mono fun _ _ _ hy => hUV hy⟩

/--
theorem `Filter.HasBasis.filter_totallyBounded_iff` / 定理 `Filter.HasBasis.filter_totallyBounded_iff`

English:
theorem Filter.HasBasis.filter_totallyBounded_iff
  statement: {ι} {p : ι -> Prop} {U : ι -> SetRel α α}
  proof: H.forall_iff fun _ _ _ h =>
h.imp fun _ ht => ⟨ht.1, f.mem_of_superset ht.2 by gcongr⟩

中文:
定理 Filter.HasBasis.filter_totallyBounded_iff
  结论: {ι} {p : ι -> 命题} {U : ι -> SetRel α α}
  证明: H.forall_iff fun _ _ _ h =>
h.imp fun _ ht => ⟨ht.1, f.mem_of_superset ht.2 by gcongr⟩

Depends on / 依赖: H.forall_iff, f.mem_of_superset, forall_iff, h.imp, mem_of_superset
-/
theorem Filter.HasBasis.filter_totallyBounded_iff {ι} {p : ι -> Prop} {U : ι -> SetRel α α}
    (H : (𝓤 α).HasBasis p U) {f : Filter α} :
    f.TotallyBounded ↔ forall i, p i -> exists t : Set α, Set.Finite t ∧ (U i).preimage t in f :=
  H.forall_iff fun _ _ _ h =>
h.imp fun _ ht => ⟨ht.1, f.mem_of_superset ht.2 by gcongr⟩

/--
theorem `totallyBounded_of_forall_isSymm` / 定理 `totallyBounded_of_forall_isSymm`

English:
theorem totallyBounded_of_forall_isSymm
  statement: {s : Set α}
  proof: UniformSpace.hasBasis_symmetric.totallyBounded_iff.2 fun V ⟨_, _⟩ => by
    simpa only [ball_eq_of_symmetry] using! h V ‹_› ‹_›

中文:
定理 totallyBounded_of_forall_isSymm
  结论: {s : Set α}
  证明: UniformSpace.hasBasis_symmetric.totallyBounded_iff.2 fun V ⟨_, _⟩ => by
    simpa only [ball_eq_of_symmetry] using! h V ‹_› ‹_›

Depends on / 依赖: UniformSpace, UniformSpace.hasBasis_symmetric.totallyBounded_iff, ball_eq_of_symmetry, hasBasis_symmetric, totallyBounded_iff
-/
theorem totallyBounded_of_forall_isSymm {s : Set α}
    (h : forall V in 𝓤 α, SetRel.IsSymm V -> exists t : Set α, Set.Finite t ∧ s subseteq ⋃ y in t, ball y V) :
    TotallyBounded s :=
  UniformSpace.hasBasis_symmetric.totallyBounded_iff.2 fun V ⟨_, _⟩ => by
    simpa only [ball_eq_of_symmetry] using! h V ‹_› ‹_›

/--
theorem `TotallyBounded.subset` / 定理 `TotallyBounded.subset`

English:
theorem TotallyBounded.subset
  given: {s₁ s₂ : Set α} (hs : s₁ subseteq s₂) (h : TotallyBounded s₂)
  proof: fun d hd =>
  let ⟨t, ht₁, ht₂⟩ := h d hd
  ⟨t, ht₁, Subset.trans hs ht₂⟩

中文:
定理 TotallyBounded.subset
  条件: {s₁ s₂ : Set α} (hs : s₁ subseteq s₂) (h : TotallyBounded s₂)
  证明: fun d hd =>
  let ⟨t, ht₁, ht₂⟩ := h d hd
  ⟨t, ht₁, Subset.trans hs ht₂⟩
-/
theorem TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ subseteq s₂) (h : TotallyBounded s₂) :
    TotallyBounded s₁ := fun d hd =>
  let ⟨t, ht₁, ht₂⟩ := h d hd
  ⟨t, ht₁, Subset.trans hs ht₂⟩

/--
theorem `Filter.TotallyBounded.mono` / 定理 `Filter.TotallyBounded.mono`

English:
theorem Filter.TotallyBounded.mono
  given: {f g : Filter α} (h : f <= g) (hg : g.TotallyBounded)
  proof: fun U hU => (hg U hU).imp fun _ => And.imp_right (@h _)

中文:
定理 Filter.TotallyBounded.mono
  条件: {f g : Filter α} (h : f <= g) (hg : g.TotallyBounded)
  证明: fun U hU => (hg U hU).imp fun _ => And.imp_right (@h _)

Depends on / 依赖: And.imp_right, imp_right
-/
theorem Filter.TotallyBounded.mono {f g : Filter α} (h : f <= g) (hg : g.TotallyBounded) :
    f.TotallyBounded :=
  fun U hU => (hg U hU).imp fun _ => And.imp_right (@h _)

/--
theorem `Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt` / 定理 `Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt`

English:
theorem Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt
  statement: {f : Filter α}
  proof: by
  refine uniformity_hasBasis_closed.totallyBounded_iff.2 fun V hV => ?_
  obtain ⟨t, htf, hst⟩ := h V hV.1
  refine ⟨t, htf, fun x hx => ?_⟩
  rw [← SetRel.preimage_eq_biUnion]; rw [id]; rw [← (hV.2.relPreimage_of_finite htf).closure_eq]
  exact hx.mem_closure_of_mem _ hst

@[deprecated (since :=

中文:
定理 Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt
  结论: {f : Filter α}
  证明: by
  refine uniformity_hasBasis_closed.totallyBounded_iff.2 fun V hV => ?_
  obtain ⟨t, htf, hst⟩ := h V hV.1
  refine ⟨t, htf, fun x hx => ?_⟩
  rw [← SetRel.preimage_eq_biUnion]; rw [id]; rw [← (hV.2.relPreimage_of_finite htf).closure_eq]
  exact hx.mem_closure_of_mem _ hst

@[deprecated (since :=

Depends on / 依赖: SetRel, SetRel.preimage_eq_biUnion, closure_eq, hx.mem_closure_of_mem, mem_closure_of_mem, preimage_eq_biUnion, relPreimage_of_finite, totallyBounded_iff, uniformity_hasBasis_closed, uniformity_hasBasis_closed.totallyBounded_iff
-/
theorem Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt {f : Filter α}
    (h : f.TotallyBounded) :
    TotallyBounded {x | ClusterPt x f} := by
  refine uniformity_hasBasis_closed.totallyBounded_iff.2 fun V hV => ?_
  obtain ⟨t, htf, hst⟩ := h V hV.1
  refine ⟨t, htf, fun x hx => ?_⟩
  rw [← SetRel.preimage_eq_biUnion]; rw [id]; rw [← (hV.2.relPreimage_of_finite htf).closure_eq]
  exact hx.mem_closure_of_mem _ hst

@[deprecated (since := "2026-07-09")]
alias Filter.TotallyBounded.totallyBounded_setOf_clusterPt :=
  Filter.TotallyBounded.totallyBounded_setOfPred_clusterPt

/--
theorem `TotallyBounded.closure` / 定理 `TotallyBounded.closure`

English:
theorem TotallyBounded.closure
  given: {s : Set α} (h : TotallyBounded s)
  statement: TotallyBounded (closure s)
  proof: by
  rw [closure_eq_cluster_pts]
  exact (Filter.totallyBounded_principal_iff.mpr h).totallyBounded_setOfPred_clusterPt

@[simp]

中文:
定理 TotallyBounded.closure
  条件: {s : Set α} (h : TotallyBounded s)
  结论: TotallyBounded (closure s)
  证明: by
  rw [closure_eq_cluster_pts]
  exact (Filter.totallyBounded_principal_iff.mpr h).totallyBounded_setOfPred_clusterPt

@[simp]

Depends on / 依赖: Filter, Filter.totallyBounded_principal_iff.mpr, closure_eq_cluster_pts, totallyBounded_principal_iff, totallyBounded_setOfPred_clusterPt
-/
theorem TotallyBounded.closure {s : Set α} (h : TotallyBounded s) : TotallyBounded (closure s) := by
  rw [closure_eq_cluster_pts]
  exact (Filter.totallyBounded_principal_iff.mpr h).totallyBounded_setOfPred_clusterPt

@[simp]
/--
lemma `totallyBounded_closure` / 引理 `totallyBounded_closure`

English:
lemma totallyBounded_closure
  given: {s : Set α}
  statement: TotallyBounded (closure s) ↔ TotallyBounded s
  proof: ⟨fun h => h.subset subset_closure, TotallyBounded.closure⟩

@[simp]

中文:
引理 totallyBounded_closure
  条件: {s : Set α}
  结论: TotallyBounded (closure s) ↔ TotallyBounded s
  证明: ⟨fun h => h.subset subset_closure, TotallyBounded.closure⟩

@[simp]

Depends on / 依赖: TotallyBounded, TotallyBounded.closure, closure, h.subset, subset, subset_closure
-/
lemma totallyBounded_closure {s : Set α} : TotallyBounded (closure s) ↔ TotallyBounded s :=
  ⟨fun h => h.subset subset_closure, TotallyBounded.closure⟩

@[simp]
/--
lemma `Filter.totallyBounded_iSup` / 引理 `Filter.totallyBounded_iSup`

English:
lemma Filter.totallyBounded_iSup
  given: {ι : Sort*} [Finite ι] {f : ι -> Filter α}
  proof: by
  refine ⟨fun h i => h.mono (le_iSup _ _), fun h U hU => ?_⟩
  choose t htf ht using (h · U hU)
  refine ⟨⋃ i, t i, finite_iUnion htf, ?_⟩
  simp_rw [U.preimage_iUnion, ← le_principal_iff, ← iSup_principal] at ht ⊢
  gcongr; apply ht

中文:
引理 Filter.totallyBounded_iSup
  条件: {ι : Sort*} [Finite ι] {f : ι -> Filter α}
  证明: by
  refine ⟨fun h i => h.mono (le_iSup _ _), fun h U hU => ?_⟩
  choose t htf ht using (h · U hU)
  refine ⟨⋃ i, t i, finite_iUnion htf, ?_⟩
  simp_rw [U.preimage_iUnion, ← le_principal_iff, ← iSup_principal] at ht ⊢
  gcongr; apply ht

Depends on / 依赖: U.preimage_iUnion, finite_iUnion, h.mono, iSup_principal, le_iSup, le_principal_iff, preimage_iUnion, simp_rw
-/
lemma Filter.totallyBounded_iSup {ι : Sort*} [Finite ι] {f : ι -> Filter α} :
    (⨆ i, f i).TotallyBounded ↔ forall i, (f i).TotallyBounded := by
  refine ⟨fun h i => h.mono (le_iSup _ _), fun h U hU => ?_⟩
  choose t htf ht using (h · U hU)
  refine ⟨⋃ i, t i, finite_iUnion htf, ?_⟩
  simp_rw [U.preimage_iUnion, ← le_principal_iff, ← iSup_principal] at ht ⊢
  gcongr; apply ht

/--
lemma `Filter.totallyBounded_biSup` / 引理 `Filter.totallyBounded_biSup`

English:
lemma Filter.totallyBounded_biSup
  given: {ι : Type*} {I : Set ι} (hI : I.Finite) {f : ι -> Filter α}
  proof: by
  have := hI.to_subtype
  rw [iSup_subtype']; rw [totallyBounded_iSup]; rw [Subtype.forall]

中文:
引理 Filter.totallyBounded_biSup
  条件: {ι : 类型} {I : Set ι} (hI : I.Finite) {f : ι -> Filter α}
  证明: by
  have := hI.to_subtype
  rw [iSup_subtype']; rw [totallyBounded_iSup]; rw [Subtype.forall]

Depends on / 依赖: Subtype, Subtype.forall, hI.to_subtype, iSup_subtype, to_subtype, totallyBounded_iSup
-/
lemma Filter.totallyBounded_biSup {ι : Type*} {I : Set ι} (hI : I.Finite) {f : ι -> Filter α} :
    (⨆ i in I, f i).TotallyBounded ↔ forall i in I, (f i).TotallyBounded := by
  have := hI.to_subtype
  rw [iSup_subtype']; rw [totallyBounded_iSup]; rw [Subtype.forall]

/--
lemma `totallyBounded_sSup` / 引理 `totallyBounded_sSup`

English:
lemma totallyBounded_sSup
  given: {S : Set (Filter α)} (hS : S.Finite)
  proof: by
  rw [sSup_eq_iSup]; rw [totallyBounded_biSup hS]

中文:
引理 totallyBounded_sSup
  条件: {S : Set (Filter α)} (hS : S.Finite)
  证明: by
  rw [sSup_eq_iSup]; rw [totallyBounded_biSup hS]

Depends on / 依赖: sSup_eq_iSup, totallyBounded_biSup
-/
lemma totallyBounded_sSup {S : Set (Filter α)} (hS : S.Finite) :
    (sSup S).TotallyBounded ↔ forall f in S, f.TotallyBounded := by
  rw [sSup_eq_iSup]; rw [totallyBounded_biSup hS]

/-- A finite indexed union is totally bounded
if and only if each set of the family is totally bounded. -/
@[simp]
/--
lemma `totallyBounded_iUnion` / 引理 `totallyBounded_iUnion`

English:
lemma totallyBounded_iUnion
  given: {ι : Sort*} [Finite ι] {s : ι -> Set α}
  proof: by
  simp_rw [← Filter.totallyBounded_principal_iff, ← Filter.iSup_principal,
    Filter.totallyBounded_iSup]

中文:
引理 totallyBounded_iUnion
  条件: {ι : Sort*} [Finite ι] {s : ι -> Set α}
  证明: by
  simp_rw [← Filter.totallyBounded_principal_iff, ← Filter.iSup_principal,
    Filter.totallyBounded_iSup]

Depends on / 依赖: Filter, Filter.iSup_principal, Filter.totallyBounded_iSup, Filter.totallyBounded_principal_iff, iSup_principal, simp_rw, totallyBounded_iSup, totallyBounded_principal_iff
-/
lemma totallyBounded_iUnion {ι : Sort*} [Finite ι] {s : ι -> Set α} :
    TotallyBounded (⋃ i, s i) ↔ forall i, TotallyBounded (s i) := by
  simp_rw [← Filter.totallyBounded_principal_iff, ← Filter.iSup_principal,
    Filter.totallyBounded_iSup]

/--
lemma `totallyBounded_biUnion` / 引理 `totallyBounded_biUnion`

English:
lemma totallyBounded_biUnion
  given: {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set α}
  proof: by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion]; rw [totallyBounded_iUnion]; rw [Subtype.forall]

中文:
引理 totallyBounded_biUnion
  条件: {ι : 类型} {I : Set ι} (hI : I.Finite) {s : ι -> Set α}
  证明: by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion]; rw [totallyBounded_iUnion]; rw [Subtype.forall]

Depends on / 依赖: Subtype, Subtype.forall, biUnion_eq_iUnion, hI.to_subtype, to_subtype, totallyBounded_iUnion
-/
lemma totallyBounded_biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set α} :
    TotallyBounded (⋃ i in I, s i) ↔ forall i in I, TotallyBounded (s i) := by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion]; rw [totallyBounded_iUnion]; rw [Subtype.forall]

/--
lemma `totallyBounded_sUnion` / 引理 `totallyBounded_sUnion`

English:
lemma totallyBounded_sUnion
  given: {S : Set (Set α)} (hS : S.Finite)
  proof: by
  rw [sUnion_eq_biUnion]; rw [totallyBounded_biUnion hS]

中文:
引理 totallyBounded_sUnion
  条件: {S : Set (Set α)} (hS : S.Finite)
  证明: by
  rw [sUnion_eq_biUnion]; rw [totallyBounded_biUnion hS]

Depends on / 依赖: sUnion_eq_biUnion, totallyBounded_biUnion
-/
lemma totallyBounded_sUnion {S : Set (Set α)} (hS : S.Finite) :
    TotallyBounded (⋃₀ S) ↔ forall s in S, TotallyBounded s := by
  rw [sUnion_eq_biUnion]; rw [totallyBounded_biUnion hS]

/--
lemma `Set.Finite.totallyBounded` / 引理 `Set.Finite.totallyBounded`

English:
lemma Set.Finite.totallyBounded
  given: {s : Set α} (hs : s.Finite)
  statement: TotallyBounded s
  proof: fun _U hU =>
⟨s, hs, fun _x hx => mem_biUnion hx refl_mem_uniformity hU⟩

中文:
引理 Set.Finite.totallyBounded
  条件: {s : Set α} (hs : s.Finite)
  结论: TotallyBounded s
  证明: fun _U hU =>
⟨s, hs, fun _x hx => mem_biUnion hx refl_mem_uniformity hU⟩
-/
lemma Set.Finite.totallyBounded {s : Set α} (hs : s.Finite) : TotallyBounded s := fun _U hU =>
⟨s, hs, fun _x hx => mem_biUnion hx refl_mem_uniformity hU⟩

/--
lemma `Set.Subsingleton.totallyBounded` / 引理 `Set.Subsingleton.totallyBounded`

English:
lemma Set.Subsingleton.totallyBounded
  given: {s : Set α} (hs : s.Subsingleton)
  proof: hs.finite.totallyBounded

@[simp]

中文:
引理 Set.Subsingleton.totallyBounded
  条件: {s : Set α} (hs : s.Subsingleton)
  证明: hs.finite.totallyBounded

@[simp]

Depends on / 依赖: finite, hs.finite.totallyBounded, totallyBounded
-/
lemma Set.Subsingleton.totallyBounded {s : Set α} (hs : s.Subsingleton) :
    TotallyBounded s :=
  hs.finite.totallyBounded

@[simp]
/--
lemma `totallyBounded_singleton` / 引理 `totallyBounded_singleton`

English:
lemma totallyBounded_singleton
  given: (a : α)
  statement: TotallyBounded {a}
  proof: (finite_singleton a).totallyBounded

@[simp]

中文:
引理 totallyBounded_singleton
  条件: (a : α)
  结论: TotallyBounded {a}
  证明: (finite_singleton a).totallyBounded

@[simp]

Depends on / 依赖: finite_singleton, totallyBounded
-/
lemma totallyBounded_singleton (a : α) : TotallyBounded {a} := (finite_singleton a).totallyBounded

@[simp]
/--
theorem `totallyBounded_empty` / 定理 `totallyBounded_empty`

English:
theorem totallyBounded_empty
  statement: TotallyBounded (∅ : Set α)
  proof: finite_empty.totallyBounded

@[simp]

中文:
定理 totallyBounded_empty
  结论: TotallyBounded (∅ : Set α)
  证明: finite_empty.totallyBounded

@[simp]

Depends on / 依赖: finite_empty, finite_empty.totallyBounded, totallyBounded
-/
theorem totallyBounded_empty : TotallyBounded (∅ : Set α) := finite_empty.totallyBounded

@[simp]
/--
theorem `Filter.totallyBounded_bot` / 定理 `Filter.totallyBounded_bot`

English:
theorem Filter.totallyBounded_bot
  statement: (⊥ : Filter α).TotallyBounded
  proof: by
  rw [← principal_empty]; rw [totallyBounded_principal_iff]
  exact totallyBounded_empty

中文:
定理 Filter.totallyBounded_bot
  结论: (⊥ : Filter α).TotallyBounded
  证明: by
  rw [← principal_empty]; rw [totallyBounded_principal_iff]
  exact totallyBounded_empty

Depends on / 依赖: principal_empty, totallyBounded_empty, totallyBounded_principal_iff
-/
theorem Filter.totallyBounded_bot : (⊥ : Filter α).TotallyBounded := by
  rw [← principal_empty]; rw [totallyBounded_principal_iff]
  exact totallyBounded_empty

/-- The union of two sets is totally bounded
if and only if each of the two sets is totally bounded. -/
@[simp]
/--
lemma `totallyBounded_union` / 引理 `totallyBounded_union`

English:
lemma totallyBounded_union
  given: {s t : Set α}
  proof: by
  rw [union_eq_iUnion]; rw [totallyBounded_iUnion]
  simp [and_comm]

中文:
引理 totallyBounded_union
  条件: {s t : Set α}
  证明: by
  rw [union_eq_iUnion]; rw [totallyBounded_iUnion]
  simp [and_comm]

Depends on / 依赖: and_comm, totallyBounded_iUnion, union_eq_iUnion
-/
lemma totallyBounded_union {s t : Set α} :
    TotallyBounded (s union t) ↔ TotallyBounded s ∧ TotallyBounded t := by
  rw [union_eq_iUnion]; rw [totallyBounded_iUnion]
  simp [and_comm]

/--
lemma `TotallyBounded.union` / 引理 `TotallyBounded.union`

English:
lemma TotallyBounded.union
  given: {s t : Set α} (hs : TotallyBounded s) (ht : TotallyBounded t)
  proof: totallyBounded_union.2 ⟨hs, ht⟩

@[simp]

中文:
引理 TotallyBounded.union
  条件: {s t : Set α} (hs : TotallyBounded s) (ht : TotallyBounded t)
  证明: totallyBounded_union.2 ⟨hs, ht⟩

@[simp]
-/
protected lemma TotallyBounded.union {s t : Set α} (hs : TotallyBounded s) (ht : TotallyBounded t) :
    TotallyBounded (s union t) :=
  totallyBounded_union.2 ⟨hs, ht⟩

@[simp]
/--
lemma `totallyBounded_insert` / 引理 `totallyBounded_insert`

English:
lemma totallyBounded_insert
  given: (a : α) {s : Set α}
  proof: by
  simp_rw [← singleton_union, totallyBounded_union, totallyBounded_singleton, true_and]

protected alias ⟨_, TotallyBounded.insert⟩ := totallyBounded_insert

@[simp]

中文:
引理 totallyBounded_insert
  条件: (a : α) {s : Set α}
  证明: by
  simp_rw [← singleton_union, totallyBounded_union, totallyBounded_singleton, true_and]

protected alias ⟨_, TotallyBounded.insert⟩ := totallyBounded_insert

@[simp]

Depends on / 依赖: simp_rw, singleton_union, totallyBounded_singleton, totallyBounded_union, true_and
-/
lemma totallyBounded_insert (a : α) {s : Set α} :
    TotallyBounded (insert a s) ↔ TotallyBounded s := by
  simp_rw [← singleton_union, totallyBounded_union, totallyBounded_singleton, true_and]

protected alias ⟨_, TotallyBounded.insert⟩ := totallyBounded_insert

@[simp]
/--
lemma `Filter.totallyBounded_sup` / 引理 `Filter.totallyBounded_sup`

English:
lemma Filter.totallyBounded_sup
  given: {f g : Filter α}
  proof: by
  rw [sup_eq_iSup]; rw [totallyBounded_iSup]
  simp [and_comm]

中文:
引理 Filter.totallyBounded_sup
  条件: {f g : Filter α}
  证明: by
  rw [sup_eq_iSup]; rw [totallyBounded_iSup]
  simp [and_comm]

Depends on / 依赖: and_comm, sup_eq_iSup, totallyBounded_iSup
-/
lemma Filter.totallyBounded_sup {f g : Filter α} :
    (f ⊔ g).TotallyBounded ↔ f.TotallyBounded ∧ g.TotallyBounded := by
  rw [sup_eq_iSup]; rw [totallyBounded_iSup]
  simp [and_comm]

/--
lemma `Filter.TotallyBounded.sup` / 引理 `Filter.TotallyBounded.sup`

English:
lemma Filter.TotallyBounded.sup
  given: {f g : Filter α} (hf : f.TotallyBounded) (hg : g.TotallyBounded)
  proof: totallyBounded_sup.2 ⟨hf, hg⟩

中文:
引理 Filter.TotallyBounded.sup
  条件: {f g : Filter α} (hf : f.TotallyBounded) (hg : g.TotallyBounded)
  证明: totallyBounded_sup.2 ⟨hf, hg⟩

Depends on / 依赖: totallyBounded_sup
-/
lemma Filter.TotallyBounded.sup {f g : Filter α} (hf : f.TotallyBounded) (hg : g.TotallyBounded) :
    (f ⊔ g).TotallyBounded :=
  totallyBounded_sup.2 ⟨hf, hg⟩

/--
theorem `Filter.TotallyBounded.map` / 定理 `Filter.TotallyBounded.map`

English:
theorem Filter.TotallyBounded.map
  statement: [UniformSpace β] {f : α -> β} {g : Filter α}
  proof: fun t ht =>
  let ⟨c, hfc, hct⟩ := hg _ (hf ht)
  ⟨f '' c, hfc.image f, by simpa [SetRel.preimage]⟩

中文:
定理 Filter.TotallyBounded.map
  结论: [UniformSpace β] {f : α -> β} {g : Filter α}
  证明: fun t ht =>
  let ⟨c, hfc, hct⟩ := hg _ (hf ht)
  ⟨f '' c, hfc.image f, by simpa [SetRel.preimage]⟩
-/
theorem Filter.TotallyBounded.map [UniformSpace β] {f : α -> β} {g : Filter α}
    (hg : g.TotallyBounded) (hf : UniformContinuous f) : (g.map f).TotallyBounded := fun t ht =>
  let ⟨c, hfc, hct⟩ := hg _ (hf ht)
  ⟨f '' c, hfc.image f, by simpa [SetRel.preimage]⟩

/--
theorem `TotallyBounded.image` / 定理 `TotallyBounded.image`

English:
theorem TotallyBounded.image
  statement: [UniformSpace β] {f : α -> β} {s : Set α} (hs : TotallyBounded s)
  proof: by
  simp only [← Filter.totallyBounded_principal_iff, ← Filter.map_principal] at hs ⊢
  exact hs.map hf

中文:
定理 TotallyBounded.image
  结论: [UniformSpace β] {f : α -> β} {s : Set α} (hs : TotallyBounded s)
  证明: by
  simp only [← Filter.totallyBounded_principal_iff, ← Filter.map_principal] at hs ⊢
  exact hs.map hf

Depends on / 依赖: Filter, Filter.map_principal, Filter.totallyBounded_principal_iff, hs.map, map_principal, totallyBounded_principal_iff
-/
theorem TotallyBounded.image [UniformSpace β] {f : α -> β} {s : Set α} (hs : TotallyBounded s)
    (hf : UniformContinuous f) : TotallyBounded (f '' s) := by
  simp only [← Filter.totallyBounded_principal_iff, ← Filter.map_principal] at hs ⊢
  exact hs.map hf

/--
theorem `Ultrafilter.cauchy_of_totallyBounded'` / 定理 `Ultrafilter.cauchy_of_totallyBounded'`

English:
theorem Ultrafilter.cauchy_of_totallyBounded'
  given: (f : Ultrafilter α) (hf : f.TotallyBounded)
  proof: ⟨f.neBot', fun _ ht =>
    let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht
    let ⟨i, hi, ht'_f⟩ := hf t' ht'₁
    have : exists y in i, { x | (x, y) in t' } in f := (Ultrafilter.eventually_exists_mem_iff hi).1 ht'_f
    let ⟨y, _, hif⟩ := this
    have : {x | (x, y) in t'} ×ˢ {x | (x

中文:
定理 Ultrafilter.cauchy_of_totallyBounded'
  条件: (f : Ultrafilter α) (hf : f.TotallyBounded)
  证明: ⟨f.neBot', fun _ ht =>
    let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht
    let ⟨i, hi, ht'_f⟩ := hf t' ht'₁
    have : exists y in i, { x | (x, y) in t' } in f := (Ultrafilter.eventually_exists_mem_iff hi).1 ht'_f
    let ⟨y, _, hif⟩ := this
    have : {x | (x, y) in t'} ×ˢ {x | (x

Depends on / 依赖: Subset, Subset.trans, Ultrafilter, Ultrafilter.eventually_exists_mem_iff, _symm, comp_symm_of_uniformity, eventually_exists_mem_iff, f.neBot, mem_of_superset, prod_mem_prod, subseteq
-/
theorem Ultrafilter.cauchy_of_totallyBounded' (f : Ultrafilter α) (hf : f.TotallyBounded) :
    Cauchy (f : Filter α) :=
  ⟨f.neBot', fun _ ht =>
    let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht
    let ⟨i, hi, ht'_f⟩ := hf t' ht'₁
    have : exists y in i, { x | (x, y) in t' } in f := (Ultrafilter.eventually_exists_mem_iff hi).1 ht'_f
    let ⟨y, _, hif⟩ := this
    have : {x | (x, y) in t'} ×ˢ {x | (x, y) in t'} subseteq t' ○ t' :=
      fun ⟨_, _⟩ ⟨(h₁ : (_, y) in t'), (h₂ : (_, y) in t')⟩ => ⟨y, h₁, ht'_symm h₂⟩
    mem_of_superset (prod_mem_prod hif hif) (Subset.trans this ht'_t)⟩

/--
theorem `Ultrafilter.cauchy_of_totallyBounded` / 定理 `Ultrafilter.cauchy_of_totallyBounded`

English:
theorem Ultrafilter.cauchy_of_totallyBounded
  statement: {s : Set α} (f : Ultrafilter α) (hs : TotallyBounded s)
  proof: f.cauchy_of_totallyBounded' (Filter.totallyBounded_principal_iff.mpr hs).mono h

中文:
定理 Ultrafilter.cauchy_of_totallyBounded
  结论: {s : Set α} (f : Ultrafilter α) (hs : TotallyBounded s)
  证明: f.cauchy_of_totallyBounded' (Filter.totallyBounded_principal_iff.mpr hs).mono h

Depends on / 依赖: Filter, Filter.totallyBounded_principal_iff.mpr, cauchy_of_totallyBounded, f.cauchy_of_totallyBounded, totallyBounded_principal_iff
-/
theorem Ultrafilter.cauchy_of_totallyBounded {s : Set α} (f : Ultrafilter α) (hs : TotallyBounded s)
    (h : ↑f <= 𝓟 s) : Cauchy (f : Filter α) :=
f.cauchy_of_totallyBounded' (Filter.totallyBounded_principal_iff.mpr hs).mono h

/--
theorem `Filter.totallyBounded_iff_filter` / 定理 `Filter.totallyBounded_iff_filter`

English:
theorem Filter.totallyBounded_iff_filter
  given: {g : Filter α}
  proof: by
  constructor
  · exact fun H f hf hfs => ⟨Ultrafilter.of f, Ultrafilter.of_le f,
      (Ultrafilter.of f).cauchy_of_totallyBounded' (H.mono ((Ultrafilter.of_le f).trans hfs))⟩
  · intro H d hd
    contrapose! H with hd_cover
    set f := ⨅ t : Finset α, g ⊓ 𝓟 (d.preimage t)ᶜ
    have hb : Antito

中文:
定理 Filter.totallyBounded_iff_filter
  条件: {g : Filter α}
  证明: by
  constructor
  · exact fun H f hf hfs => ⟨Ultrafilter.of f, Ultrafilter.of_le f,
      (Ultrafilter.of f).cauchy_of_totallyBounded' (H.mono ((Ultrafilter.of_le f).trans hfs))⟩
  · intro H d hd
    contrapose! H with hd_cover
    set f := ⨅ t : Finset α, g ⊓ 𝓟 (d.preimage t)ᶜ
    have hb : Antito
-/
protected theorem Filter.totallyBounded_iff_filter {g : Filter α} :
    g.TotallyBounded ↔ forall f, NeBot f -> f <= g -> exists c <= f, Cauchy c := by
  constructor
  · exact fun H f hf hfs => ⟨Ultrafilter.of f, Ultrafilter.of_le f,
      (Ultrafilter.of f).cauchy_of_totallyBounded' (H.mono ((Ultrafilter.of_le f).trans hfs))⟩
  · intro H d hd
    contrapose! H with hd_cover
    set f := ⨅ t : Finset α, g ⊓ 𝓟 (d.preimage t)ᶜ
    have hb : Antitone fun t : Finset α => g ⊓ 𝓟 (d.preimage t)ᶜ :=
      fun s t (h : s subseteq t) => by beta_reduce; gcongr
    have : Filter.NeBot f :=
      (Filter.iInf_neBot_iff_of_directed' <| hb.directed_ge).mpr fun t =>
Filter.notMem_iff_inf_principal_compl.mp hd_cover t t.finite_toSet
    have : f <= g := iInf_le_of_le ∅ (by simp)
    refine ⟨f, ‹_›, ‹_›, fun c hcf hc => ?_⟩
    rcases mem_prod_same_iff.1 (hc.2 hd) with ⟨m, hm, hmd⟩
    rcases hc.1.nonempty_of_mem hm with ⟨y, hym⟩
    have : {x | (x, y) in d}ᶜ in c := by
simpa [SetRel.preimage] using hcf.trans (iInf_le _ {y}).trans inf_le_right
    rcases hc.1.nonempty_of_mem (inter_mem hm this) with ⟨z, hzm, hyz⟩
    exact hyz (hmd ⟨hzm, hym⟩)

/--
theorem `Filter.totallyBounded_iff_ultrafilter` / 定理 `Filter.totallyBounded_iff_ultrafilter`

English:
theorem Filter.totallyBounded_iff_ultrafilter
  given: {g : Filter α}
  proof: by
refine ⟨fun hg f hf => f.cauchy_of_totallyBounded' hg.mono hf,
    fun H => g.totallyBounded_iff_filter.2 ?_⟩
  intro f hf hfs
  exact ⟨Ultrafilter.of f, Ultrafilter.of_le f, H _ ((Ultrafilter.of_le f).trans hfs)⟩

中文:
定理 Filter.totallyBounded_iff_ultrafilter
  条件: {g : Filter α}
  证明: by
refine ⟨fun hg f hf => f.cauchy_of_totallyBounded' hg.mono hf,
    fun H => g.totallyBounded_iff_filter.2 ?_⟩
  intro f hf hfs
  exact ⟨Ultrafilter.of f, Ultrafilter.of_le f, H _ ((Ultrafilter.of_le f).trans hfs)⟩
-/
protected theorem Filter.totallyBounded_iff_ultrafilter {g : Filter α} :
    g.TotallyBounded ↔ forall f : Ultrafilter α, ↑f <= g -> Cauchy (f : Filter α) := by
refine ⟨fun hg f hf => f.cauchy_of_totallyBounded' hg.mono hf,
    fun H => g.totallyBounded_iff_filter.2 ?_⟩
  intro f hf hfs
  exact ⟨Ultrafilter.of f, Ultrafilter.of_le f, H _ ((Ultrafilter.of_le f).trans hfs)⟩

/--
theorem `totallyBounded_iff_filter` / 定理 `totallyBounded_iff_filter`

English:
theorem totallyBounded_iff_filter
  given: {s : Set α}
  proof: by
  rw [← Filter.totallyBounded_principal_iff]; rw [Filter.totallyBounded_iff_filter]

中文:
定理 totallyBounded_iff_filter
  条件: {s : Set α}
  证明: by
  rw [← Filter.totallyBounded_principal_iff]; rw [Filter.totallyBounded_iff_filter]

Depends on / 依赖: Filter, Filter.totallyBounded_iff_filter, Filter.totallyBounded_principal_iff, totallyBounded_iff_filter, totallyBounded_principal_iff
-/
theorem totallyBounded_iff_filter {s : Set α} :
    TotallyBounded s ↔ forall f, NeBot f -> f <= 𝓟 s -> exists c <= f, Cauchy c := by
  rw [← Filter.totallyBounded_principal_iff]; rw [Filter.totallyBounded_iff_filter]

/--
theorem `totallyBounded_iff_ultrafilter` / 定理 `totallyBounded_iff_ultrafilter`

English:
theorem totallyBounded_iff_ultrafilter
  given: {s : Set α}
  proof: by
  rw [← Filter.totallyBounded_principal_iff]; rw [Filter.totallyBounded_iff_ultrafilter]

中文:
定理 totallyBounded_iff_ultrafilter
  条件: {s : Set α}
  证明: by
  rw [← Filter.totallyBounded_principal_iff]; rw [Filter.totallyBounded_iff_ultrafilter]

Depends on / 依赖: Filter, Filter.totallyBounded_iff_ultrafilter, Filter.totallyBounded_principal_iff, totallyBounded_iff_ultrafilter, totallyBounded_principal_iff
-/
theorem totallyBounded_iff_ultrafilter {s : Set α} :
    TotallyBounded s ↔ forall f : Ultrafilter α, ↑f <= 𝓟 s -> Cauchy (f : Filter α) := by
  rw [← Filter.totallyBounded_principal_iff]; rw [Filter.totallyBounded_iff_ultrafilter]

/--
theorem `isCompact_iff_totallyBounded_isComplete` / 定理 `isCompact_iff_totallyBounded_isComplete`

English:
theorem isCompact_iff_totallyBounded_isComplete
  given: {s : Set α}
  proof: ⟨fun hs =>
    ⟨totallyBounded_iff_ultrafilter.2 fun f hf =>
        let ⟨_, _, fx⟩ := isCompact_iff_ultrafilter_le_nhds.1 hs f hf
        cauchy_nhds.mono fx,
      fun f fc fs =>
      let ⟨a, as, fa⟩ := @hs f fc.1 fs
      ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
    fun ⟨ht, hc⟩ =>
    isCompact_

中文:
定理 isCompact_iff_totallyBounded_isComplete
  条件: {s : Set α}
  证明: ⟨fun hs =>
    ⟨totallyBounded_iff_ultrafilter.2 fun f hf =>
        let ⟨_, _, fx⟩ := isCompact_iff_ultrafilter_le_nhds.1 hs f hf
        cauchy_nhds.mono fx,
      fun f fc fs =>
      let ⟨a, as, fa⟩ := @hs f fc.1 fs
      ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
    fun ⟨ht, hc⟩ =>
    isCompact_

Depends on / 依赖: cauchy_nhds, cauchy_nhds.mono, isCompact_iff_ultrafilter_le_nhds, le_nhds_of_cauchy_adhp, totallyBounded_iff_ultrafilter
-/
theorem isCompact_iff_totallyBounded_isComplete {s : Set α} :
    IsCompact s ↔ TotallyBounded s ∧ IsComplete s :=
  ⟨fun hs =>
    ⟨totallyBounded_iff_ultrafilter.2 fun f hf =>
        let ⟨_, _, fx⟩ := isCompact_iff_ultrafilter_le_nhds.1 hs f hf
        cauchy_nhds.mono fx,
      fun f fc fs =>
      let ⟨a, as, fa⟩ := @hs f fc.1 fs
      ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
    fun ⟨ht, hc⟩ =>
    isCompact_iff_ultrafilter_le_nhds.2 fun f hf =>
      hc _ (totallyBounded_iff_ultrafilter.1 ht f hf) hf⟩

/--
theorem `IsCompact.totallyBounded` / 定理 `IsCompact.totallyBounded`

English:
theorem IsCompact.totallyBounded
  given: {s : Set α} (h : IsCompact s)
  statement: TotallyBounded s
  proof: (isCompact_iff_totallyBounded_isComplete.1 h).1

中文:
定理 IsCompact.totallyBounded
  条件: {s : Set α} (h : IsCompact s)
  结论: TotallyBounded s
  证明: (isCompact_iff_totallyBounded_isComplete.1 h).1
-/
protected theorem IsCompact.totallyBounded {s : Set α} (h : IsCompact s) : TotallyBounded s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).1

/--
theorem `IsCompact.isComplete` / 定理 `IsCompact.isComplete`

English:
theorem IsCompact.isComplete
  given: {s : Set α} (h : IsCompact s)
  statement: IsComplete s
  proof: (isCompact_iff_totallyBounded_isComplete.1 h).2

中文:
定理 IsCompact.isComplete
  条件: {s : Set α} (h : IsCompact s)
  结论: IsComplete s
  证明: (isCompact_iff_totallyBounded_isComplete.1 h).2
-/
protected theorem IsCompact.isComplete {s : Set α} (h : IsCompact s) : IsComplete s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).2

-- see Note [lower instance priority]
instance (priority := 100) complete_of_compact {α : Type u} [UniformSpace α] [CompactSpace α] :
    CompleteSpace α :=
  ⟨fun hf => by simpa using (isCompact_iff_totallyBounded_isComplete.1 isCompact_univ).2 _ hf⟩

/--
theorem `TotallyBounded.isCompact_of_isComplete` / 定理 `TotallyBounded.isCompact_of_isComplete`

English:
theorem TotallyBounded.isCompact_of_isComplete
  statement: {s : Set α} (ht : TotallyBounded s)
  proof: isCompact_iff_totallyBounded_isComplete.mpr ⟨ht, hc⟩

中文:
定理 TotallyBounded.isCompact_of_isComplete
  结论: {s : Set α} (ht : TotallyBounded s)
  证明: isCompact_iff_totallyBounded_isComplete.mpr ⟨ht, hc⟩

Depends on / 依赖: isCompact_iff_totallyBounded_isComplete, isCompact_iff_totallyBounded_isComplete.mpr
-/
theorem TotallyBounded.isCompact_of_isComplete {s : Set α} (ht : TotallyBounded s)
    (hc : IsComplete s) : IsCompact s := isCompact_iff_totallyBounded_isComplete.mpr ⟨ht, hc⟩

/--
theorem `TotallyBounded.isCompact_of_isClosed` / 定理 `TotallyBounded.isCompact_of_isClosed`

English:
theorem TotallyBounded.isCompact_of_isClosed
  statement: [CompleteSpace α] {s : Set α} (ht : TotallyBounded s)
  proof: ht.isCompact_of_isComplete hc.isComplete

中文:
定理 TotallyBounded.isCompact_of_isClosed
  结论: [CompleteSpace α] {s : Set α} (ht : TotallyBounded s)
  证明: ht.isCompact_of_isComplete hc.isComplete

Depends on / 依赖: hc.isComplete, ht.isCompact_of_isComplete, isCompact_of_isComplete, isComplete
-/
theorem TotallyBounded.isCompact_of_isClosed [CompleteSpace α] {s : Set α} (ht : TotallyBounded s)
    (hc : IsClosed s) : IsCompact s := ht.isCompact_of_isComplete hc.isComplete

/--
theorem `Filter.TotallyBounded.isCompact_setOfPred_clusterPt` / 定理 `Filter.TotallyBounded.isCompact_setOfPred_clusterPt`

English:
theorem Filter.TotallyBounded.isCompact_setOfPred_clusterPt
  proof: hf.totallyBounded_setOfPred_clusterPt.isCompact_of_isClosed isClosed_setOfPred_clusterPt

@[deprecated (since := "2026-07-09")]
alias Filter.TotallyBounded.isCompact_setOf_clusterPt :=
  Filter.TotallyBounded.isCompact_setOfPred_clusterPt

中文:
定理 Filter.TotallyBounded.isCompact_setOfPred_clusterPt
  证明: hf.totallyBounded_setOfPred_clusterPt.isCompact_of_isClosed isClosed_setOfPred_clusterPt

@[deprecated (since := "2026-07-09")]
alias Filter.TotallyBounded.isCompact_setOf_clusterPt :=
  Filter.TotallyBounded.isCompact_setOfPred_clusterPt

Depends on / 依赖: hf.totallyBounded_setOfPred_clusterPt.isCompact_of_isClosed, isClosed_setOfPred_clusterPt, isCompact_of_isClosed, totallyBounded_setOfPred_clusterPt
-/
theorem Filter.TotallyBounded.isCompact_setOfPred_clusterPt
    [CompleteSpace α] {f : Filter α} (hf : f.TotallyBounded) : IsCompact {x | ClusterPt x f} :=
  hf.totallyBounded_setOfPred_clusterPt.isCompact_of_isClosed isClosed_setOfPred_clusterPt

@[deprecated (since := "2026-07-09")]
alias Filter.TotallyBounded.isCompact_setOf_clusterPt :=
  Filter.TotallyBounded.isCompact_setOfPred_clusterPt

/--
theorem `Filter.TotallyBounded.exists_clusterPt` / 定理 `Filter.TotallyBounded.exists_clusterPt`

English:
theorem Filter.TotallyBounded.exists_clusterPt
  proof: by
  let m := Ultrafilter.of f
  have hmf : m <= f := Ultrafilter.of_le f
  have hm := m.cauchy_of_totallyBounded' (hf.mono hmf)
  obtain ⟨x, hx⟩ := CompleteSpace.complete hm
  rw [le_nhds_iff_adhp_of_cauchy hm] at hx
  exact ⟨x, hx.mono hmf⟩

中文:
定理 Filter.TotallyBounded.exists_clusterPt
  证明: by
  let m := Ultrafilter.of f
  have hmf : m <= f := Ultrafilter.of_le f
  have hm := m.cauchy_of_totallyBounded' (hf.mono hmf)
  obtain ⟨x, hx⟩ := CompleteSpace.complete hm
  rw [le_nhds_iff_adhp_of_cauchy hm] at hx
  exact ⟨x, hx.mono hmf⟩

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, Ultrafilter, Ultrafilter.of, Ultrafilter.of_le, cauchy_of_totallyBounded, complete, hf.mono, hx.mono, le_nhds_iff_adhp_of_cauchy, m.cauchy_of_totallyBounded, of_le
-/
theorem Filter.TotallyBounded.exists_clusterPt
    [CompleteSpace α] {f : Filter α} [f.NeBot] (hf : f.TotallyBounded) : exists x, ClusterPt x f := by
  let m := Ultrafilter.of f
  have hmf : m <= f := Ultrafilter.of_le f
  have hm := m.cauchy_of_totallyBounded' (hf.mono hmf)
  obtain ⟨x, hx⟩ := CompleteSpace.complete hm
  rw [le_nhds_iff_adhp_of_cauchy hm] at hx
  exact ⟨x, hx.mono hmf⟩

/--
theorem `CauchySeq.totallyBounded_range` / 定理 `CauchySeq.totallyBounded_range`

English:
theorem CauchySeq.totallyBounded_range
  given: {s : Nat -> α} (hs : CauchySeq s)
  proof: by
  intro a ha
  obtain ⟨n, hn⟩ := cauchySeq_iff.1 hs a ha
  refine ⟨s '' { k | k <= n }, (finite_le_nat _).image _, ?_⟩
  rw [range_subset_iff]; rw [biUnion_image]
  intro m
  rw [mem_iUnion₂]
  rcases le_total m n with hm | hm
  exacts [⟨m, hm, refl_mem_uniformity ha⟩, ⟨n, le_refl n, hn m hm n le

中文:
定理 CauchySeq.totallyBounded_range
  条件: {s : 自然数 -> α} (hs : CauchySeq s)
  证明: by
  intro a ha
  obtain ⟨n, hn⟩ := cauchySeq_iff.1 hs a ha
  refine ⟨s '' { k | k <= n }, (finite_le_nat _).image _, ?_⟩
  rw [range_subset_iff]; rw [biUnion_image]
  intro m
  rw [mem_iUnion₂]
  rcases le_total m n with hm | hm
  exacts [⟨m, hm, refl_mem_uniformity ha⟩, ⟨n, le_refl n, hn m hm n le

Depends on / 依赖: biUnion_image, cauchySeq_iff, exacts, finite_le_nat, le_refl, le_rfl, le_total, range_subset_iff, refl_mem_uniformity
-/
theorem CauchySeq.totallyBounded_range {s : Nat -> α} (hs : CauchySeq s) :
    TotallyBounded (range s) := by
  intro a ha
  obtain ⟨n, hn⟩ := cauchySeq_iff.1 hs a ha
  refine ⟨s '' { k | k <= n }, (finite_le_nat _).image _, ?_⟩
  rw [range_subset_iff]; rw [biUnion_image]
  intro m
  rw [mem_iUnion₂]
  rcases le_total m n with hm | hm
  exacts [⟨m, hm, refl_mem_uniformity ha⟩, ⟨n, le_refl n, hn m hm n le_rfl⟩]

/--
Definition of `interUnionBalls` / `interUnionBalls` 的定义

English:
definition interUnionBalls
  signature: (xs : Nat -> α) (u : Nat -> Nat) (V : Nat -> SetRel α α)
  body: ⋂ n, ⋃ m <= u n, UniformSpace.ball (xs m) (Prod.swap ⁻¹' V n)

中文:
定义 interUnionBalls
  签名: (xs : 自然数 -> α) (u : 自然数 -> 自然数) (V : 自然数 -> SetRel α α)
  定义体: ⋂ n, ⋃ m <= u n, UniformSpace.ball (xs m) (Prod.swap ⁻¹' V n)

Depends on / 依赖: Prod.swap, UniformSpace, UniformSpace.ball
-/
def interUnionBalls (xs : Nat -> α) (u : Nat -> Nat) (V : Nat -> SetRel α α) : Set α :=
  ⋂ n, ⋃ m <= u n, UniformSpace.ball (xs m) (Prod.swap ⁻¹' V n)

/--
lemma `totallyBounded_interUnionBalls` / 引理 `totallyBounded_interUnionBalls`

English:
lemma totallyBounded_interUnionBalls
  statement: {p : Nat -> Prop} {U : Nat -> SetRel α α}
  proof: by
  rw [Filter.HasBasis.totallyBounded_iff H]
  intro i _
  have h_subset : interUnionBalls xs u U
      subseteq ⋃ m <= u i, UniformSpace.ball (xs m) (Prod.swap ⁻¹' U i) :=
    fun x hx => Set.mem_iInter.1 hx i
  classical
  refine ⟨Finset.image xs (Finset.range (u i + 1)), Finset.finite_toSet _, 

中文:
引理 totallyBounded_interUnionBalls
  结论: {p : 自然数 -> 命题} {U : 自然数 -> SetRel α α}
  证明: by
  rw [Filter.HasBasis.totallyBounded_iff H]
  intro i _
  have h_subset : interUnionBalls xs u U
      subseteq ⋃ m <= u i, UniformSpace.ball (xs m) (Prod.swap ⁻¹' U i) :=
    fun x hx => Set.mem_iInter.1 hx i
  classical
  refine ⟨Finset.image xs (Finset.range (u i + 1)), Finset.finite_toSet _, 

Depends on / 依赖: Filter, Filter.HasBasis.totallyBounded_iff, Finset, Finset.coe_image, Finset.coe_range, Finset.finite_toSet, Finset.image, Finset.range, HasBasis, Nat.lt_succ_iff, Prod.swap, Set.mem_iInter, UniformSpace, UniformSpace.ball, biUnion_and, classical, coe_image, coe_range, finite_toSet, h_subset
-/
lemma totallyBounded_interUnionBalls {p : Nat -> Prop} {U : Nat -> SetRel α α}
    (H : (uniformity α).HasBasis p U) (xs : Nat -> α) (u : Nat -> Nat) :
    TotallyBounded (interUnionBalls xs u U) := by
  rw [Filter.HasBasis.totallyBounded_iff H]
  intro i _
  have h_subset : interUnionBalls xs u U
      subseteq ⋃ m <= u i, UniformSpace.ball (xs m) (Prod.swap ⁻¹' U i) :=
    fun x hx => Set.mem_iInter.1 hx i
  classical
  refine ⟨Finset.image xs (Finset.range (u i + 1)), Finset.finite_toSet _, fun x hx => ?_⟩
  simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio, iUnion_exists, biUnion_and',
    iUnion_iUnion_eq_right, Nat.lt_succ_iff]
  exact h_subset hx

/--
theorem `isCompact_closure_interUnionBalls` / 定理 `isCompact_closure_interUnionBalls`

English:
theorem isCompact_closure_interUnionBalls
  statement: {p : Nat -> Prop} {U : Nat -> SetRel α α}
  proof: by
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  exact totallyBounded_interUnionBalls H xs u

中文:
定理 isCompact_closure_interUnionBalls
  结论: {p : 自然数 -> 命题} {U : 自然数 -> SetRel α α}
  证明: by
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  exact totallyBounded_interUnionBalls H xs u

Depends on / 依赖: TotallyBounded, TotallyBounded.closure, closure, isClosed_closure, isClosed_closure.isComplete, isCompact_iff_totallyBounded_isComplete, isComplete, totallyBounded_interUnionBalls
-/
theorem isCompact_closure_interUnionBalls {p : Nat -> Prop} {U : Nat -> SetRel α α}
    (H : (uniformity α).HasBasis p U) [CompleteSpace α] (xs : Nat -> α) (u : Nat -> Nat) :
    IsCompact (closure (interUnionBalls xs u U)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  exact totallyBounded_interUnionBalls H xs u

/-!
### Sequentially complete space

In this section we prove that a uniform space is complete provided that it is sequentially complete
(i.e., any Cauchy sequence converges) and its uniformity filter admits a countable generating set.
In particular, this applies to (e)metric spaces, see the files
`Mathlib/Topology/EMetricSpace/Basic.lean` and `Mathlib/Topology/MetricSpace/Basic.lean`.

More precisely, we assume that there is a sequence of entourages `U_n` such that any other
entourage includes one of `U_n`. Then any Cauchy filter `f` generates a decreasing sequence of
sets `s_n ∈ f` such that `s_n × s_n ⊆ U_n`. Choose a sequence `x_n∈s_n`. It is easy to show
that this is a Cauchy sequence. If this sequence converges to some `a`, then `f ≤ 𝓝 a`. -/


namespace SequentiallyComplete

variable {f : Filter α} (hf : Cauchy f) {U : Nat -> SetRel α α} (U_mem : forall n, U n in 𝓤 α)

open Set Finset

noncomputable section

/--
Definition of `setSeqAux` / `setSeqAux` 的定义

English:
definition setSeqAux
  signature: (n : Nat)
  body: Classical.indefiniteDescription _ (cauchy_iff.1 hf).2 (U n) (U_mem n)

中文:
定义 setSeqAux
  签名: (n : 自然数)
  定义体: Classical.indefiniteDescription _ (cauchy_iff.1 hf).2 (U n) (U_mem n)

Depends on / 依赖: Classical, Classical.indefiniteDescription, U_mem, cauchy_iff, indefiniteDescription
-/
def setSeqAux (n : Nat) : { s : Set α // s in f ∧ s ×ˢ s subseteq U n } :=
Classical.indefiniteDescription _ (cauchy_iff.1 hf).2 (U n) (U_mem n)

/--
Definition of `setSeq` / `setSeq` 的定义

English:
definition setSeq
  signature: (n : Nat)
  body: ⋂ m in Set.Iic n, (setSeqAux hf U_mem m).val

中文:
定义 setSeq
  签名: (n : 自然数)
  定义体: ⋂ m in Set.Iic n, (setSeqAux hf U_mem m).val

Depends on / 依赖: Set.Iic, U_mem, setSeqAux
-/
def setSeq (n : Nat) : Set α :=
  ⋂ m in Set.Iic n, (setSeqAux hf U_mem m).val

/--
theorem `setSeq_mem` / 定理 `setSeq_mem`

English:
theorem setSeq_mem
  given: (n : Nat)
  statement: setSeq hf U_mem n in f
  proof: (biInter_mem (finite_le_nat n)).2 fun m _ => (setSeqAux hf U_mem m).2.1

中文:
定理 setSeq_mem
  条件: (n : 自然数)
  结论: setSeq hf U_mem n in f
  证明: (biInter_mem (finite_le_nat n)).2 fun m _ => (setSeqAux hf U_mem m).2.1

Depends on / 依赖: U_mem, biInter_mem, finite_le_nat, setSeqAux
-/
theorem setSeq_mem (n : Nat) : setSeq hf U_mem n in f :=
  (biInter_mem (finite_le_nat n)).2 fun m _ => (setSeqAux hf U_mem m).2.1

/--
theorem `setSeq_mono` / 定理 `setSeq_mono`

English:
theorem setSeq_mono
  given: ⦃m n
  statement: Nat⦄ (h : m <= n) : setSeq hf U_mem n subseteq setSeq hf U_mem m
  proof: biInter_subset_biInter_left Iic_subset_Iic.2 h

中文:
定理 setSeq_mono
  条件: ⦃m n
  结论: 自然数⦄ (h : m <= n) : setSeq hf U_mem n subseteq setSeq hf U_mem m
  证明: biInter_subset_biInter_left Iic_subset_Iic.2 h

Depends on / 依赖: Iic_subset_Iic, biInter_subset_biInter_left
-/
theorem setSeq_mono ⦃m n : Nat⦄ (h : m <= n) : setSeq hf U_mem n subseteq setSeq hf U_mem m :=
biInter_subset_biInter_left Iic_subset_Iic.2 h

/--
theorem `setSeq_sub_aux` / 定理 `setSeq_sub_aux`

English:
theorem setSeq_sub_aux
  given: (n : Nat)
  statement: setSeq hf U_mem n subseteq setSeqAux hf U_mem n
  proof: biInter_subset_of_mem self_mem_Iic

中文:
定理 setSeq_sub_aux
  条件: (n : 自然数)
  结论: setSeq hf U_mem n subseteq setSeqAux hf U_mem n
  证明: biInter_subset_of_mem self_mem_Iic

Depends on / 依赖: biInter_subset_of_mem, self_mem_Iic
-/
theorem setSeq_sub_aux (n : Nat) : setSeq hf U_mem n subseteq setSeqAux hf U_mem n :=
  biInter_subset_of_mem self_mem_Iic

/--
theorem `setSeq_prod_subset` / 定理 `setSeq_prod_subset`

English:
theorem setSeq_prod_subset
  given: {N m n} (hm : N <= m) (hn : N <= n)
  proof: fun p hp => by
  refine (setSeqAux hf U_mem N).2.2 ⟨?_, ?_⟩ <;> apply setSeq_sub_aux
  · exact setSeq_mono hf U_mem hm hp.1
  · exact setSeq_mono hf U_mem hn hp.2

中文:
定理 setSeq_prod_subset
  条件: {N m n} (hm : N <= m) (hn : N <= n)
  证明: fun p hp => by
  refine (setSeqAux hf U_mem N).2.2 ⟨?_, ?_⟩ <;> apply setSeq_sub_aux
  · exact setSeq_mono hf U_mem hm hp.1
  · exact setSeq_mono hf U_mem hn hp.2

Depends on / 依赖: U_mem, setSeqAux, setSeq_mono, setSeq_sub_aux
-/
theorem setSeq_prod_subset {N m n} (hm : N <= m) (hn : N <= n) :
    setSeq hf U_mem m ×ˢ setSeq hf U_mem n subseteq U N := fun p hp => by
  refine (setSeqAux hf U_mem N).2.2 ⟨?_, ?_⟩ <;> apply setSeq_sub_aux
  · exact setSeq_mono hf U_mem hm hp.1
  · exact setSeq_mono hf U_mem hn hp.2

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: (n : Nat)
  body: (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose

中文:
定义 seq
  签名: (n : 自然数)
  定义体: (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose

Depends on / 依赖: U_mem, nonempty_of_mem, setSeq_mem
-/
def seq (n : Nat) : α :=
  (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose

/--
theorem `seq_mem` / 定理 `seq_mem`

English:
theorem seq_mem
  given: (n : Nat)
  statement: seq hf U_mem n in setSeq hf U_mem n
  proof: (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose_spec

中文:
定理 seq_mem
  条件: (n : 自然数)
  结论: seq hf U_mem n in setSeq hf U_mem n
  证明: (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose_spec

Depends on / 依赖: U_mem, choose_spec, nonempty_of_mem, setSeq_mem
-/
theorem seq_mem (n : Nat) : seq hf U_mem n in setSeq hf U_mem n :=
  (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose_spec

/--
theorem `seq_pair_mem` / 定理 `seq_pair_mem`

English:
theorem seq_pair_mem
  given: ⦃N m n
  statement: Nat⦄ (hm : N <= m) (hn : N <= n) :
  proof: setSeq_prod_subset hf U_mem hm hn ⟨seq_mem hf U_mem m, seq_mem hf U_mem n⟩

中文:
定理 seq_pair_mem
  条件: ⦃N m n
  结论: 自然数⦄ (hm : N <= m) (hn : N <= n) :
  证明: setSeq_prod_subset hf U_mem hm hn ⟨seq_mem hf U_mem m, seq_mem hf U_mem n⟩

Depends on / 依赖: U_mem, seq_mem, setSeq_prod_subset
-/
theorem seq_pair_mem ⦃N m n : Nat⦄ (hm : N <= m) (hn : N <= n) :
    (seq hf U_mem m, seq hf U_mem n) in U N :=
  setSeq_prod_subset hf U_mem hm hn ⟨seq_mem hf U_mem m, seq_mem hf U_mem n⟩

/--
theorem `seq_is_cauchySeq` / 定理 `seq_is_cauchySeq`

English:
theorem seq_is_cauchySeq
  given: (U_le : forall s in 𝓤 α, exists n, U n subseteq s)
  statement: CauchySeq seq hf U_mem
  proof: cauchySeq_of_controlled U U_le seq_pair_mem hf U_mem

中文:
定理 seq_is_cauchySeq
  条件: (U_le : 对任意 s in 𝓤 α, 存在 n, U n subseteq s)
  结论: CauchySeq seq hf U_mem
  证明: cauchySeq_of_controlled U U_le seq_pair_mem hf U_mem

Depends on / 依赖: U_le, U_mem, cauchySeq_of_controlled, seq_pair_mem
-/
theorem seq_is_cauchySeq (U_le : forall s in 𝓤 α, exists n, U n subseteq s) : CauchySeq seq hf U_mem :=
cauchySeq_of_controlled U U_le seq_pair_mem hf U_mem

/--
theorem `le_nhds_of_seq_tendsto_nhds` / 定理 `le_nhds_of_seq_tendsto_nhds`

English:
theorem le_nhds_of_seq_tendsto_nhds
  statement: (U_le : forall s in 𝓤 α, exists n, U n subseteq s)
  proof: le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      rcases U_le s hs with ⟨m, hm⟩
      rcases tendsto_atTop'.1 ha _ (mem_nhds_left a (U_mem m)) with ⟨n, hn⟩
      refine
        ⟨setSeq hf U_mem (max m n), setSeq_mem hf U_mem _, ?_, seq hf U_mem (max m n), ?_,
          seq_mem hf U_mem _⟩
      ·

中文:
定理 le_nhds_of_seq_tendsto_nhds
  结论: (U_le : 对任意 s in 𝓤 α, 存在 n, U n subseteq s)
  证明: le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      rcases U_le s hs with ⟨m, hm⟩
      rcases tendsto_atTop'.1 ha _ (mem_nhds_left a (U_mem m)) with ⟨n, hn⟩
      refine
        ⟨setSeq hf U_mem (max m n), setSeq_mem hf U_mem _, ?_, seq hf U_mem (max m n), ?_,
          seq_mem hf U_mem _⟩
      ·

Depends on / 依赖: Set.Subset.trans, Subset, U_le, U_mem, le_max_left, le_max_right, le_nhds_of_cauchy_adhp_aux, mem_nhds_left, seq_mem, setSeq, setSeq_mem, setSeq_prod_subset, tendsto_atTop
-/
theorem le_nhds_of_seq_tendsto_nhds (U_le : forall s in 𝓤 α, exists n, U n subseteq s)
    ⦃a : α⦄ (ha : Tendsto (seq hf U_mem) atTop (𝓝 a)) : f <= 𝓝 a :=
  le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      rcases U_le s hs with ⟨m, hm⟩
      rcases tendsto_atTop'.1 ha _ (mem_nhds_left a (U_mem m)) with ⟨n, hn⟩
      refine
        ⟨setSeq hf U_mem (max m n), setSeq_mem hf U_mem _, ?_, seq hf U_mem (max m n), ?_,
          seq_mem hf U_mem _⟩
      · have := le_max_left m n
        exact Set.Subset.trans (setSeq_prod_subset hf U_mem this this) hm
      · exact hm (hn _ <| le_max_right m n))

end

end SequentiallyComplete

namespace UniformSpace

open SequentiallyComplete

variable [IsCountablyGenerated (𝓤 α)]

/--
theorem `complete_of_convergent_controlled_sequences` / 定理 `complete_of_convergent_controlled_sequences`

English:
theorem complete_of_convergent_controlled_sequences
  statement: (U : Nat -> SetRel α α) (U_mem : forall n, U n in 𝓤 α)
  proof: by
  obtain ⟨U', -, hU'⟩ := (𝓤 α).exists_antitone_seq
  have Hmem : forall n, U n inter U' n in 𝓤 α := fun n => inter_mem (U_mem n) (hU'.2 ⟨n, Subset.refl _⟩)
refine ⟨fun hf => (HU (seq hf Hmem) fun N m n hm hn => ?_).imp
    le_nhds_of_seq_tendsto_nhds _ _ fun s hs => ?_⟩
  · exact inter_subset_lef

中文:
定理 complete_of_convergent_controlled_sequences
  结论: (U : 自然数 -> SetRel α α) (U_mem : 对任意 n, U n in 𝓤 α)
  证明: by
  obtain ⟨U', -, hU'⟩ := (𝓤 α).exists_antitone_seq
  have Hmem : forall n, U n inter U' n in 𝓤 α := fun n => inter_mem (U_mem n) (hU'.2 ⟨n, Subset.refl _⟩)
refine ⟨fun hf => (HU (seq hf Hmem) fun N m n hm hn => ?_).imp
    le_nhds_of_seq_tendsto_nhds _ _ fun s hs => ?_⟩
  · exact inter_subset_lef

Depends on / 依赖: Subset, Subset.refl, Subset.trans, U_mem, exists_antitone_seq, inter_mem, inter_subset_left, inter_subset_right, le_nhds_of_seq_tendsto_nhds, seq_pair_mem
-/
theorem complete_of_convergent_controlled_sequences (U : Nat -> SetRel α α) (U_mem : forall n, U n in 𝓤 α)
    (HU : forall u : Nat -> α, (forall N m n, N <= m -> N <= n -> (u m, u n) in U N) -> exists a, Tendsto u atTop (𝓝 a)) :
    CompleteSpace α := by
  obtain ⟨U', -, hU'⟩ := (𝓤 α).exists_antitone_seq
  have Hmem : forall n, U n inter U' n in 𝓤 α := fun n => inter_mem (U_mem n) (hU'.2 ⟨n, Subset.refl _⟩)
refine ⟨fun hf => (HU (seq hf Hmem) fun N m n hm hn => ?_).imp
    le_nhds_of_seq_tendsto_nhds _ _ fun s hs => ?_⟩
  · exact inter_subset_left (seq_pair_mem hf Hmem hm hn)
  · rcases hU'.1 hs with ⟨N, hN⟩
    exact ⟨N, Subset.trans inter_subset_right hN⟩

/--
theorem `complete_of_cauchySeq_tendsto` / 定理 `complete_of_cauchySeq_tendsto`

English:
theorem complete_of_cauchySeq_tendsto
  given: (H' : forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a))
  proof: let ⟨U', _, hU'⟩ := (𝓤 α).exists_antitone_seq
  complete_of_convergent_controlled_sequences U' (fun n => hU'.2 ⟨n, Subset.refl _⟩) fun u hu =>
H' u cauchySeq_of_controlled U' (fun _ hs => hU'.1 hs) hu

中文:
定理 complete_of_cauchySeq_tendsto
  条件: (H' : 对任意 u : 自然数 -> α, CauchySeq u -> 存在 a, Tendsto u atTop (𝓝 a))
  证明: let ⟨U', _, hU'⟩ := (𝓤 α).exists_antitone_seq
  complete_of_convergent_controlled_sequences U' (fun n => hU'.2 ⟨n, Subset.refl _⟩) fun u hu =>
H' u cauchySeq_of_controlled U' (fun _ hs => hU'.1 hs) hu

Depends on / 依赖: Subset, Subset.refl, cauchySeq_of_controlled, complete_of_convergent_controlled_sequences, exists_antitone_seq
-/
theorem complete_of_cauchySeq_tendsto (H' : forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) :
    CompleteSpace α :=
  let ⟨U', _, hU'⟩ := (𝓤 α).exists_antitone_seq
  complete_of_convergent_controlled_sequences U' (fun n => hU'.2 ⟨n, Subset.refl _⟩) fun u hu =>
H' u cauchySeq_of_controlled U' (fun _ hs => hU'.1 hs) hu

variable (α)

-- TODO: move to `Topology.UniformSpace.Basic`
instance (priority := 100) firstCountableTopology : FirstCountableTopology α :=
  ⟨fun a => by rw [nhds_eq_comap_uniformity]; infer_instance⟩

/--
Instance `secondCountable_of_separable` / 实例 `secondCountable_of_separable`

English:
instance secondCountable_of_separable
  signature: [SeparableSpace α]
  body: by
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩
  obtain
    ⟨t : Nat -> SetRel α α, hto : forall i : Nat, t i in (𝓤 α).sets ∧ IsOpen (t i) ∧ (t i).IsSymm,
      h_basis : (𝓤 α).HasAntitoneBasis t⟩ :=
    (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
  choose ht_mem hto 

中文:
实例 secondCountable_of_separable
  签名: [SeparableSpace α]
  定义体: by
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩
  obtain
    ⟨t : Nat -> SetRel α α, hto : forall i : Nat, t i in (𝓤 α).sets ∧ IsOpen (t i) ∧ (t i).IsSymm,
      h_basis : (𝓤 α).HasAntitoneBasis t⟩ :=
    (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
  choose ht_mem hto 

Depends on / 依赖: HasAntitoneBasis, IsOpen, IsSymm, SetRel, biUnion, countable_range, eq_generateFrom, exists_antitone_subbasis, exists_countable_dense, h_basis, hsc.biUnion, ht_mem, isTopologicalBasis_of_isOpen_of_nhds, mem_range, uniformity_hasBasis_open_symmetric
-/
instance secondCountable_of_separable [SeparableSpace α] : SecondCountableTopology α := by
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩
  obtain
    ⟨t : Nat -> SetRel α α, hto : forall i : Nat, t i in (𝓤 α).sets ∧ IsOpen (t i) ∧ (t i).IsSymm,
      h_basis : (𝓤 α).HasAntitoneBasis t⟩ :=
    (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
  choose ht_mem hto hts using hto
  refine ⟨⟨⋃ x in s, range fun k => ball x (t k), hsc.biUnion fun x _ => countable_range _, ?_⟩⟩
  refine (isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).eq_generateFrom
  · simp only [mem_iUnion₂, mem_range]
    rintro _ ⟨x, _, k, rfl⟩
    exact isOpen_ball x (hto k)
  · intro x V hxV hVo
    simp only [mem_iUnion₂, mem_range, exists_prop]
    rcases UniformSpace.mem_nhds_iff.1 (IsOpen.mem_nhds hVo hxV) with ⟨U, hU, hUV⟩
    rcases comp_symm_of_uniformity hU with ⟨U', hU', _, hUU'⟩
    rcases h_basis.toHasBasis.mem_iff.1 hU' with ⟨k, -, hk⟩
    rcases hsd.inter_open_nonempty (ball x <| t k) (isOpen_ball x (hto k))
        ⟨x, UniformSpace.mem_ball_self _ (ht_mem k)⟩ with
      ⟨y, hxy, hys⟩
    refine ⟨_, ⟨y, hys, k, rfl⟩, (t k).symm hxy, fun z hz => ?_⟩
    exact hUV (ball_subset_of_comp_subset (hk hxy) hUU' (hk hz))

variable {α}

/--
theorem `subset_countable_closure_of_almost_dense_set` / 定理 `subset_countable_closure_of_almost_dense_set`

English:
theorem subset_countable_closure_of_almost_dense_set
  statement: (s : Set α)
  proof: by
  obtain ⟨B, hB, _⟩ := has_seq_basis α
  replace hs (n : Nat) := hs (B n) (hB.mem n)
  choose t tC ht using hs
  have := fun n => (tC n).to_subtype
  choose o hox hos using fun (n : Nat) (x : t n) (hx : (ball x.1 (B n) inter s).Nonempty) => hx
  refine ⟨⋃ (n) (x), range (o n x), iUnion₂_subset fu

中文:
定理 subset_countable_closure_of_almost_dense_set
  结论: (s : Set α)
  证明: by
  obtain ⟨B, hB, _⟩ := has_seq_basis α
  replace hs (n : Nat) := hs (B n) (hB.mem n)
  choose t tC ht using hs
  have := fun n => (tC n).to_subtype
  choose o hox hos using fun (n : Nat) (x : t n) (hx : (ball x.1 (B n) inter s).Nonempty) => hx
  refine ⟨⋃ (n) (x), range (o n x), iUnion₂_subset fu

Depends on / 依赖: Nonempty, comp_mem_uniformity_sets, countable_iUnion, countable_range, hB.mem, has_seq_basis, mem_closure_iff_ball, range_subset_iff, replace, to_subtype
-/
theorem subset_countable_closure_of_almost_dense_set (s : Set α)
    (hs : forall U in 𝓤 α, exists t : Set α, t.Countable ∧ s subseteq ⋃ x in t, ball x U) :
    exists t, t subseteq s ∧ t.Countable ∧ s subseteq closure t := by
  obtain ⟨B, hB, _⟩ := has_seq_basis α
  replace hs (n : Nat) := hs (B n) (hB.mem n)
  choose t tC ht using hs
  have := fun n => (tC n).to_subtype
  choose o hox hos using fun (n : Nat) (x : t n) (hx : (ball x.1 (B n) inter s).Nonempty) => hx
  refine ⟨⋃ (n) (x), range (o n x), iUnion₂_subset fun _ _ => range_subset_iff.2 (hos _ _),
    countable_iUnion fun _ => countable_iUnion fun _ => countable_range _, fun x hx => ?_⟩
  rw [mem_closure_iff_ball]
  intro U hU
  obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
  obtain ⟨n, hn⟩ := hB.mem_iff.1 hV
  specialize ht n hx
  rw [mem_iUnion₂] at ht
  obtain ⟨y, hy, hyx⟩ := ht
  refine ⟨o n ⟨y, hy⟩ ⟨x, hyx, hx⟩, ?_, ?_⟩
  · apply ball_mono ((SetRel.comp_subset_comp hn hn).trans hVU)
    exact mem_ball_comp (mem_ball_symmetry.2 hyx) (hox n ⟨y, hy⟩ ⟨x, hyx, hx⟩)
  · exact mem_iUnion₂_of_mem ⟨y, hy⟩ (mem_range_self ⟨x, hyx, hx⟩)

/--
theorem `secondCountable_of_almost_dense_set` / 定理 `secondCountable_of_almost_dense_set`

English:
theorem secondCountable_of_almost_dense_set
  proof: by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : forall U in 𝓤 α, exists t : Set α, Set.Countable t ∧ univ subseteq ⋃ x in t, ball x U := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this wit

中文:
定理 secondCountable_of_almost_dense_set
  证明: by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : forall U in 𝓤 α, exists t : Set α, Set.Countable t ∧ univ subseteq ⋃ x in t, ball x U := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this wit

Depends on / 依赖: Countable, SeparableSpace, Set.Countable, UniformSpace, UniformSpace.secondCountable_of_separable, mem_univ, secondCountable_of_separable, subset_countable_closure_of_almost_dense_set, subseteq, univ_subset_iff
-/
theorem secondCountable_of_almost_dense_set
    (hs : forall U in 𝓤 α, exists t : Set α, t.Countable ∧ ⋃ x in t, ball x U = univ) :
    SecondCountableTopology α := by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : forall U in 𝓤 α, exists t : Set α, Set.Countable t ∧ univ subseteq ⋃ x in t, ball x U := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this with ⟨t, -, htc, ht⟩
  exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩

/--
lemma `_root_.TotallyBounded.isSeparable` / 引理 `_root_.TotallyBounded.isSeparable`

English:
lemma _root_.TotallyBounded.isSeparable
  given: {s : Set α} (h : TotallyBounded s)
  proof: by
  obtain ⟨t, -, htc, hts⟩ := subset_countable_closure_of_almost_dense_set s fun U hU => by
    obtain ⟨t, ht, hst⟩ := h (SetRel.inv U)
      (mem_of_superset (symmetrize_mem_uniformity hU) SetRel.symmetrize_subset_inv)
    exact ⟨t, ht.countable, hst⟩
  exact ⟨t, htc, hts⟩

中文:
引理 _root_.TotallyBounded.isSeparable
  条件: {s : Set α} (h : TotallyBounded s)
  证明: by
  obtain ⟨t, -, htc, hts⟩ := subset_countable_closure_of_almost_dense_set s fun U hU => by
    obtain ⟨t, ht, hst⟩ := h (SetRel.inv U)
      (mem_of_superset (symmetrize_mem_uniformity hU) SetRel.symmetrize_subset_inv)
    exact ⟨t, ht.countable, hst⟩
  exact ⟨t, htc, hts⟩

Depends on / 依赖: SetRel, SetRel.inv, SetRel.symmetrize_subset_inv, countable, ht.countable, mem_of_superset, subset_countable_closure_of_almost_dense_set, symmetrize_mem_uniformity, symmetrize_subset_inv
-/
lemma _root_.TotallyBounded.isSeparable {s : Set α} (h : TotallyBounded s) :
    TopologicalSpace.IsSeparable s := by
  obtain ⟨t, -, htc, hts⟩ := subset_countable_closure_of_almost_dense_set s fun U hU => by
    obtain ⟨t, ht, hst⟩ := h (SetRel.inv U)
      (mem_of_superset (symmetrize_mem_uniformity hU) SetRel.symmetrize_subset_inv)
    exact ⟨t, ht.countable, hst⟩
  exact ⟨t, htc, hts⟩

end UniformSpace
