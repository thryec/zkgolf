import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MainTheorems
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqX
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModLazyG
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModLazyGT
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.WindowCaps
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqD
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModBalGT

/-!
# 24-bit-limb parameter bundle (`B = 24`, `m = 171`, `W = 33`)

Parameters for the `B = 24` rearchitecture of the 4096-bit RSA circuit:

* `171` limbs of `24` bits: values occupy at most `4096 = 170·24 + 16` bits, so
  the top limb of every *value* is tight at width `tb = 16` (bound `2^4096`),
  and the lazy-reduction quotients fit the same `m` limbs with a
  `tb+2 = 18`-bit top limb.
* Carry width `W = 33`: the carry offset is
  `(m+1)·(2^B+2) = 172·(2^24+2) ≈ 2^31.43`, so `2·OFF < 2^33`.
* Byte alignment is preserved: `24` bits = 3 bytes, and `512 = 170·3 + 2`
  bytes, so the top limb is exactly 2 bytes (`2^16 = 2^tb`).
* Grouped carries admit `g = 9` (`Bg = 216`; dominant field term ≈ `2^249 < p`).
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface

/-- Number of 24-bit limbs covering the 4096-bit values *and* the
lazy-reduction quotients: `171` (`170` full limbs below a 16-bit top limb). -/
abbrev numLimbs24 : ℕ := 171

instance : NeZero numLimbs24 := ⟨by decide⟩

/-- Big-integer parameters for 4096-bit RSA over the circom prime at `B = 24`:
171 limbs, 33-bit carries. -/
def bigIntParams24 : BigIntParams circomPrime numLimbs24 where
  B := 24
  W := 33
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide

/-- RSA parameters at `B = 24` with public exponent `e = 65536 = 2^16`: the pure
squaring chain of the `e = 65537` pipeline (the final multiply-by-`base` is fused
into the top-level `MulModTo`). -/
def params24sq : RSAParams circomPrime numLimbs24 where
  bigIntParams := bigIntParams24
  e := 65536

/-- Tight top-limb width of the 24-bit chain: values are `< 2^4096 = 2^(170·24 + 16)`. -/
theorem htb24 : 1 ≤ 16 ∧ (2 : ℕ) ^ 16 < circomPrime := ⟨by decide, by decide⟩

/-- `16 + 1 ≤ 24` (slack-2 squaring-quotient top-limb width). -/
theorem htbB24sq : 16 + 1 ≤ params24sq.bigIntParams.B := by decide

/-! ## Fused-final parameters (`a²·b ≡ em`, quotient over `2m` limbs)

The fused final step asserts `a²·sig = q·n + em` in one grouped equality: with
`a < 2^4096` and `sig < n` the quotient satisfies `q < 2^8192 = 2^(341·24 + 8)`,
so it occupies `342` limbs with an 8-bit top limb — no slack lemma needed. -/

/-- Number of 24-bit limbs of the fused-final quotient: `342` (`341` full limbs
below an 8-bit top limb, `8192 = 341·24 + 8`). -/
abbrev numLimbs24q : ℕ := 342

instance : NeZero numLimbs24q := ⟨by decide⟩

/-- Big-integer parameters at `B = 24` over `342` limbs, used only for the
fused-final quotient's `NormalizeTight` battery. Carry width `W = 34`: the
offset is `343·(2^24+2) ≈ 2^32.4`, so `2·OFF < 2^34`. -/
def bigIntParams24q : BigIntParams circomPrime numLimbs24q where
  B := 24
  W := 34
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide

/-- Fused-final quotient top-limb width: `q < 2^8192 = 2^(341·24 + 8)`. -/
theorem htq8 : 1 ≤ 8 ∧ (2 : ℕ) ^ 8 < circomPrime := ⟨by decide, by decide⟩

/-- RSA parameters at `B = 24` with `e = 32768 = 2^15`: the squaring chain of the
fused `e = 65537` pipeline, whose final step asserts `(sig^32768)²·sig ≡ em`. -/
def params24sq15 : RSAParams circomPrime numLimbs24 where
  bigIntParams := bigIntParams24
  e := 32768

/-- Grouped-equality parameters for the fused-final triple-product equality over
`3m−1 = 512` coefficients: coefficient bound `N = 171²·2^72` (a triple-convolution
coefficient is `< m²·2^(3B)`), offset `OFF = 2^63−1` (`N ≤ (2^24−1)·OFF`, and
`2·OFF < 2^64`), carry width `W = 64`. -/
def eqXParams24 : GroupedEqX.EqXParams circomPrime where
  B := 24
  W := 64
  N := 171 ^ 2 * 2 ^ 72
  OFF := 2 ^ 63 - 1
  hB1 := by decide
  hNpos := by decide
  hOFFpos := by decide
  hNO := by decide
  hWB := by decide
  hB := by decide
  hW := by decide

/-- Grouping hypotheses for the fused-final equality at group size `g = 7`
(`Bg = 168`; dominant field term ≈ `2^233.4 < p`). -/
theorem hgx24 : GroupedEqX.GXHyps circomPrime 24 64 (171 ^ 2 * 2 ^ 72) (2 ^ 63 - 1) 7 :=
  ⟨by decide, by decide, by decide⟩

/-- Fused-final quotient-fit exponent bound: `2·tb ≤ B + tq` at
`tb = 16, B = 24, tq = 8` (exact equality: `a² < 2^8192 = 2^(341·24+8)`). -/
theorem htbq24 : 2 * 16 ≤ 24 + 8 := by decide

/-- Triple-convolution coefficient bound fits the field: `171²·2^72 < p`. -/
theorem hNp24 : (171 : ℕ) ^ 2 * 2 ^ 72 < circomPrime := by decide

/-! ## Graduated carry parameters for the `B = 24` squaring equalities -/

/-- Tent-shaped per-coefficient bound: `min(j+1, 2m−1−j)` convolution terms of
`(2^24−1)²` each, plus one remainder limb (`< 2^24`) on the low positions. On
the last checked carry group (`j ∈ [324, 332]`) the top-limb-aware bound
applies instead: two of the window products carry tight top limbs (quotient
top `< 2^17`, input/modulus top `< 2^16`), so the group's coefficients — and
with them the final checked carry — shrink by one bit. -/
def nf24 (j : ℕ) : ℕ :=
  if 324 ≤ j ∧ j ≤ 332 then
    (2 * numLimbs24 - 3 - j) * ((2 ^ 24 - 1) * (2 ^ 24 - 1))
      + (2 ^ (16 + 1) - 1) * (2 ^ 24 - 1) + (2 ^ 16 - 1) * (2 ^ 24 - 1) + 2 ^ 24
  else
    min (j + 1) (2 * numLimbs24 - 1 - j) * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24

/-- Per-boundary carry offsets (recursive tent bounds) for the `37` interior
group boundaries of the squaring equality at `g = 9`. -/
def offTable24 : List ℕ :=
  [150994935, 301989870, 452984805, 603979740, 754974675, 905969610, 1056964545,
   1207959480, 1358954415, 1509949350, 1660944285, 1811939220, 1962934155,
   2113929090, 2264924025, 2415918960, 2566913895, 2717908830, 2868903765,
   2717908831, 2566913896, 2415918961, 2264924026, 2113929091, 1962934156,
   1811939221, 1660944286, 1509949351, 1358954416, 1207959481, 1056964546,
   905969611, 754974676, 603979741, 452984806, 301989871, 117637113]

/-- Per-boundary carry offset function (defaults to the peak beyond the table). -/
def off24 (k : ℕ) : ℕ := offTable24.getD k 2868903765

/-- Per-boundary carry range-check widths (tent-shaped, peak `33`; the final
checked boundary narrows to `28` via the top-limb-aware last group). -/
def wTable24 : List ℕ :=
  [29, 30, 30, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33,
   33, 33, 33, 33, 32, 32, 32, 32, 32, 32, 32, 31, 31, 31, 31, 30, 30, 28]

/-- Per-boundary carry width function (defaults to the peak beyond the table). -/
def wf24 (k : ℕ) : ℕ := wTable24.getD k 33

/-- The graduated grouped-equality parameter bundle for the squaring chain. -/
def vparams24 : GroupedEqV.VParams where
  Nf := nf24
  OFFf := off24
  Wf := wf24
  Nmax := 171 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24
  OFFmax := 2868903765
  Wmax := 33

/-- All width-table entries lie in `[28, 33]`. -/
private lemma wf24_bounds (k : ℕ) : 28 ≤ wf24 k ∧ wf24 k ≤ 33 := by
  unfold wf24
  by_cases h : k < wTable24.length
  · rw [List.getD_eq_getElem _ _ h]
    have hall : ∀ x ∈ wTable24, 28 ≤ x ∧ x ≤ 33 := by decide
    exact hall _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨by norm_num, le_refl _⟩

/-- The graduated grouping hypotheses for `B = 24`, `m = 171`, `g = 9`. -/
theorem hgv24 : GroupedEqV.GVHyps circomPrime numLimbs24 24 9 vparams24 := by
  refine ⟨by norm_num, by decide, by decide, ?_, ?_, ?_, ?_, by decide⟩
  · -- widths are positive and field-bounded
    intro k
    have h := wf24_bounds k
    constructor
    · show 1 ≤ wf24 k
      omega
    · show 2 ^ wf24 k < circomPrime
      calc (2 : ℕ) ^ wf24 k ≤ 2 ^ 33 := Nat.pow_le_pow_right (by norm_num) h.2
        _ < circomPrime := by decide
  · -- Nf is positive
    intro j
    show 1 ≤ nf24 j
    unfold nf24
    have h1 : (1 : ℕ) ≤ 2 ^ 24 := by norm_num
    split <;> omega
  · -- Nf is capped by Nmax
    intro j hj
    show nf24 j ≤ 171 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24
    unfold nf24
    split
    case isTrue h =>
      have h1 : 2 * numLimbs24 - 3 - j ≤ 169 := by
        show 2 * 171 - 3 - j ≤ 169
        omega
      calc (2 * numLimbs24 - 3 - j) * ((2 ^ 24 - 1) * (2 ^ 24 - 1))
            + (2 ^ (16 + 1) - 1) * (2 ^ 24 - 1) + (2 ^ 16 - 1) * (2 ^ 24 - 1) + 2 ^ 24
          ≤ 169 * ((2 ^ 24 - 1) * (2 ^ 24 - 1))
            + (2 ^ 24 - 1) * (2 ^ 24 - 1) + (2 ^ 24 - 1) * (2 ^ 24 - 1) + 2 ^ 24 := by
            refine Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
              (Nat.mul_le_mul_right _ h1) ?_) ?_) _
            · exact Nat.mul_le_mul_right _ (by norm_num)
            · exact Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ 171 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24 := by
            have hc : 169 * ((2 ^ 24 - 1) * (2 ^ 24 - 1))
                + (2 ^ 24 - 1) * (2 ^ 24 - 1) + (2 ^ 24 - 1) * (2 ^ 24 - 1)
                  = 171 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) := by ring
            omega
    case isFalse h =>
      have hmin : min (j + 1) (2 * numLimbs24 - 1 - j) ≤ 171 := by
        have h171 : numLimbs24 = 171 := rfl
        rw [h171]
        omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hmin) _
  · -- per-boundary caps, range-fit, and the recursive offset inequalities
    decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- `Nf` adequacy for the squaring step (`NfOk`) at `tb = 16`: the top-window
form on the last checked group, the (weaker) tent form elsewhere. -/
theorem hNf24 : SquareModLazyG.NfOk (m := numLimbs24) 24 16 vparams24 := by
  have hcl : ∀ j : Fin (2 * numLimbs24 - 1),
      (if numLimbs24 - 1 ≤ j.val then
        (2 * numLimbs24 - 3 - j.val) * ((2 ^ 24 - 1) * (2 ^ 24 - 1))
          + (2 ^ (16 + 1) - 1) * (2 ^ 24 - 1) + (2 ^ 16 - 1) * (2 ^ 24 - 1) + 2 ^ 24
      else
        min (j.val + 1) (2 * numLimbs24 - 1 - j.val) * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24)
        ≤ vparams24.Nf j.val := by decide
  intro j hj
  exact hcl ⟨j, hj⟩

/-- RSA parameters at `B = 24` with `e = 16384 = 2^14`: the squaring chain after
the tight first squaring in the fused `e = 65537` pipeline. -/
def params24sq14 : RSAParams circomPrime numLimbs24 where
  bigIntParams := bigIntParams24
  e := 16384

/-- `16 + 1 ≤ 24` for the `e = 16384` parameter bundle. -/
theorem htbB24sq14 : 16 + 1 ≤ params24sq14.bigIntParams.B := by decide

/-- `16 + 1 ≤ 24` for the tight first squaring (plain `bigIntParams24`). -/
theorem htbB24sqT : 16 + 1 ≤ bigIntParams24.B := by decide


/-! ## Graduated two-sided carry parameters for the fused-final `GroupedEqXV` equality

Three stacked optimizations: (1) per-group *size schedule* — wide (`g = 8/9`)
groups on the tent fringes where the coefficient bounds are small; (2)
top-limb-aware exact tail caps (`NfL`/`NfR` switch to literal window-sum tables
at position `322`); (3) *asymmetric two-sided offsets* — the lhs triple-product
coefficients (`≈ 2^87`) dwarf the rhs `q·n` (`≈ 2^55`), so each side gets its
own recursive offset battery (`OFFP` positive/lhs, `OFFN` negative/rhs = the
witness shift) and the carry range covers `OFFN + OFFP` instead of `2·OFF`. -/

/-- Coefficient length of the fused equality: `3m − 1 = 512`. -/
abbrev numLimbsX24 : ℕ := 3 * numLimbs24 - 1

/-- Head lhs bound (`j < 322`): the triple-product triangular cap. -/
def nfXL24 (j : ℕ) : ℕ :=
  WindowCaps.triCap numLimbs24 j * ((2 ^ 24 - 1) * (2 ^ 24 - 1) * (2 ^ 24 - 1)) + 1

/-- Head rhs bound (`j < 322`): the `q·n` window cap plus one `em` limb. -/
def nfXR24 (j : ℕ) : ℕ :=
  WindowCaps.qnCap numLimbs24 j * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24

/-- Tail lhs bounds (`322 ≤ j < 512`): exact top-limb-aware triple-product
window sums plus one. -/
def nfXLtail24 : List ℕ :=
  [80208402563030933146614751, 79556771444306754749185126, 78895695594305686820928751,
   78225175013027729361845626, 77545209700472882371935751, 76855799656641145851199126,
   76156944881532519799635751, 75448645375147004217245626, 74730901137484599104028751,
   74003712168545304459985126, 73267078468329120285114751, 72521000036836046579417626,
   71765476874066083342893751, 71000508980019230575543126, 70226096354695488277365751,
   69442238998094856448361626, 68648936910217335088530751, 67846190091062924197873126,
   67048055174950731823236751, 66254642408310812004173626, 65465952007309336950523876,
   64681983971946306662287501, 63902738302221721139464501, 63128214998135580382054876,
   62358414059687884390058626, 61593335486878633163475751, 60832979279707826702306251,
   60077345438175465006550126, 59326433962281548076207376, 58580244852026075911278001,
   57838778107409048511762001, 57102033728430465877659376, 56370011715090328008970126,
   55642712067388634905694251, 54920134785325386567831751, 54202279868900582995382626,
   53489147318114224188346876, 52780737132966310146724501, 52077049313456840870515501,
   51378083859585816359719876, 50683840771353236614337626, 49994320048759101634368751,
   49309521691803411419813251, 48629445700486165970671126, 47954092074807365286942376,
   47283460814767009368627001, 46617551920365098215725001, 45956365391601631828236376,
   45299901228476610206161126, 44648159430990033349499251, 44001139999141901258250751,
   43358842932932213932415626, 42721268232360971371993876, 42088415897428173576985501,
   41460285928133820547390501, 40836878324477912283208876, 40218193086460448784440626,
   39604230214081430051085751, 38994989707340856083144251, 38390471566238726880616126,
   37790675790775042443501376, 37195602380949802771800001, 36605251336763007865512001,
   36019622658214657724637376, 35438716345304752349176126, 34862532398033291739128251,
   34291070816400275894493751, 33724331600405704815272626, 33162314750049578501464876,
   32605020265331896953070501, 32052448146252660170089501, 31504598392811868152521876,
   30961471005009520900367626, 30423065982845618413626751, 29889383326320160692299251,
   29360423035433147736385126, 28836185110184579545884376, 28316669550574456120797001,
   27801876356602777461123001, 27291805528269543566862376, 26786457065574754438015126,
   26285830968518410074581251, 25789927237100510476560751, 25298745871321055643953626,
   24812286871180045576759876, 24330550236677480274979501, 23853535967813359738612501,
   23381244064587683967658876, 22913674527000452962118626, 22450827355051666721991751,
   21992702548741325247278251, 21539300108069428537978126, 21090620033035976594091376,
   20646662323640969415618001, 20207426979884407002558001, 19772914001766289354911376,
   19343123389286616472678126, 18918055142445388355858251, 18497709261242605004451751,
   18082085745678266418458626, 17671184595752372597878876, 17265005811464923542712501,
   16863549392815919252959501, 16466815339805359728619876, 16074803652433244969693626,
   15687514330699574976180751, 15304947374604349748081251, 14927102784147569285395126,
   14553980559329233588122376, 14185580700149342656263001, 13821903206607896489817001,
   13462948078704895088784376, 13108715316440338453165126, 12759204919814226582959251,
   12414416888826559478166751, 12074351223477337138787626, 11739007923766559564821876,
   11408386989694226756269501, 11082488421260338713130501, 10761312218464895435404876,
   10444858381307896923092626, 10133126909789343176193751, 9826117803909234194708251,
   9523831063667569978636126, 9226266689064350527977376, 8933424680099575842732001,
   8645305036773245922900001, 8361907759085360768481376, 8083232847035920379476126,
   7809280300624924755884251, 7540050119852373897705751, 7275542304718267804940626,
   7015756855222606477588876, 6760693771365389915650501, 6510353053146618119125501,
   6264734700566291088013876, 6023838713624408822315626, 5787665092320971322030751,
   5556213836655978587159251, 5329484946629430617701126, 5107478422241327413656376,
   4890194263491668975025001, 4677632470380455301807001, 4469793042907686394002376,
   4266675981073362251611126, 4068281284877482874633251, 3874608954320048263068751,
   3685658989401058416917626, 3501431390120513336179876, 3321926156478413020855501,
   3147143288474757470944501, 2977082786109546686446876, 2811744649382780667362626,
   2651128878294459413691751, 2495235472844582925434251, 2344064433033151202590126,
   2197615758860164245159376, 2055889450325622053142001, 1918885507429524626538001,
   1786603930171871965347376, 1659044718552664069570126, 1536207872571900939206251,
   1418093392229582574255751, 1304701277525708974718626, 1196031528460280140594876,
   1092084145033296071884501, 992859127244756768587501, 898356475094662230703876,
   808576188583012458233626, 723518267709807451176751, 643182712475047209533251,
   567569522878731733303126, 496678698920861022486376, 430510240601435077083001,
   369064147920453897093001, 312340420877917482516376, 260339059473825833353126,
   213060063708178949603251, 170503433580976831266751, 132669169092219478343626,
   99557270241906890833876, 71167737030039068737501, 47500569456616012054501,
   28555767521637720784876, 14333331225104194928626, 4833260567015434485751,
   55555547371439456251, 216166172209840126, 281462092005376,
   1]

/-- Tail rhs bounds (`322 ≤ j < 512`): exact top-limb-aware `q·n` window sums
plus one `em` limb. -/
def nfXRtail24 : List ℕ :=
  [47851839848120491, 47851839848120491, 47851839848120491,
   47851839848120491, 47851839848120491, 47851839848120491,
   47851839848120491, 47851839848120491, 47851839848120491,
   47851839848120491, 47851839848120491, 47851839848120491,
   47851839848120491, 47851839848120491, 47851839848120491,
   47851839848120491, 47851839848120491, 47851839848120491,
   47851839848120491, 47570369183154091, 47288894239997866,
   47007419296841641, 46725944353685416, 46444469410529191,
   46162994467372966, 45881519524216741, 45600044581060516,
   45318569637904291, 45037094694748066, 44755619751591841,
   44474144808435616, 44192669865279391, 43911194922123166,
   43629719978966941, 43348245035810716, 43066770092654491,
   42785295149498266, 42503820206342041, 42222345263185816,
   41940870320029591, 41659395376873366, 41377920433717141,
   41096445490560916, 40814970547404691, 40533495604248466,
   40252020661092241, 39970545717936016, 39689070774779791,
   39407595831623566, 39126120888467341, 38844645945311116,
   38563171002154891, 38281696058998666, 38000221115842441,
   37718746172686216, 37437271229529991, 37155796286373766,
   36874321343217541, 36592846400061316, 36311371456905091,
   36029896513748866, 35748421570592641, 35466946627436416,
   35185471684280191, 34903996741123966, 34622521797967741,
   34341046854811516, 34059571911655291, 33778096968499066,
   33496622025342841, 33215147082186616, 32933672139030391,
   32652197195874166, 32370722252717941, 32089247309561716,
   31807772366405491, 31526297423249266, 31244822480093041,
   30963347536936816, 30681872593780591, 30400397650624366,
   30118922707468141, 29837447764311916, 29555972821155691,
   29274497877999466, 28993022934843241, 28711547991687016,
   28430073048530791, 28148598105374566, 27867123162218341,
   27585648219062116, 27304173275905891, 27022698332749666,
   26741223389593441, 26459748446437216, 26178273503280991,
   25896798560124766, 25615323616968541, 25333848673812316,
   25052373730656091, 24770898787499866, 24489423844343641,
   24207948901187416, 23926473958031191, 23644999014874966,
   23363524071718741, 23082049128562516, 22800574185406291,
   22519099242250066, 22237624299093841, 21956149355937616,
   21674674412781391, 21393199469625166, 21111724526468941,
   20830249583312716, 20548774640156491, 20267299697000266,
   19985824753844041, 19704349810687816, 19422874867531591,
   19141399924375366, 18859924981219141, 18578450038062916,
   18296975094906691, 18015500151750466, 17734025208594241,
   17452550265438016, 17171075322281791, 16889600379125566,
   16608125435969341, 16326650492813116, 16045175549656891,
   15763700606500666, 15482225663344441, 15200750720188216,
   14919275777031991, 14637800833875766, 14356325890719541,
   14074850947563316, 13793376004407091, 13511901061250866,
   13230426118094641, 12948951174938416, 12667476231782191,
   12386001288625966, 12104526345469741, 11823051402313516,
   11541576459157291, 11260101516001066, 10978626572844841,
   10697151629688616, 10415676686532391, 10134201743376166,
   9852726800219941, 9571251857063716, 9289776913907491,
   9008301970751266, 8726827027595041, 8445352084438816,
   8163877141282591, 7882402198126366, 7600927254970141,
   7319452311813916, 7037977368657691, 6756502425501466,
   6475027482345241, 6193552539189016, 5912077596032791,
   5630602652876566, 5349127709720341, 5067652766564116,
   4786177823407891, 4504702880251666, 4223227937095441,
   3941752993939216, 3660278050782991, 3378803107626766,
   3097328164470541, 2815853221314316, 2534378278158091,
   2252903335001866, 1971428391845641, 1689953448689416,
   1408478505533191, 1127003562376966, 845528619220741,
   564053676064516, 282578732908291, 1103789752066,
   33488641]

/-- Mixed lhs bound. -/
def nfXL24T (j : ℕ) : ℕ :=
  if j < 322 then nfXL24 j else nfXLtail24.getD (j - 322) 1

/-- Mixed rhs bound. -/
def nfXR24T (j : ℕ) : ℕ :=
  if j < 322 then nfXR24 j else nfXRtail24.getD (j - 322) (2 ^ 24)


/-- Per-group size schedule: wide (`g = 8`) left fringe (groups 0–8), `g = 7`
mid-range (9–66), `g = 8` right fringe (67–69), one `g = 9` phantom group (70)
and `g = 8` beyond. -/
def gfX24 (k : ℕ) : ℕ :=
  if k = 0 then 5 else if k < 11 then 8 else if k < 58 then 7
  else if k < 69 then 8 else if k = 69 then 9 else 8

/-- Prefix positions `posOf k = Σ_{i<k} gfX24 i`, in closed form. -/
def posOfX24 (k : ℕ) : ℕ :=
  if k = 0 then 0
  else if k ≤ 11 then 5 + 8 * (k - 1)
  else if k ≤ 58 then 85 + 7 * (k - 11)
  else if k ≤ 69 then 414 + 8 * (k - 58)
  else if k ≤ 70 then 502 + 9 * (k - 69)
  else 511 + 8 * (k - 70)

/-- Per-boundary carry range-check widths for the `70` checked boundaries
(covering `OFFN + OFFP`). -/
def wtableX24 : List ℕ :=
  [52, 55, 56, 57, 58, 59, 59, 59, 60, 60, 60, 61, 61, 61, 61, 61, 61, 62, 62, 62,
   62, 62, 62, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63,
   63, 63, 63, 63, 63, 62, 62, 62, 62, 62, 62, 62, 62, 61, 61, 61, 61, 61, 60, 60,
   60, 59, 59, 59, 58, 57, 57, 55, 53, 25]

/-- Positive-flank (lhs) recursive offsets. -/
def offtableXP24 : List ℕ :=
  [4222124063457300, 25614219609112680, 65020711516766460,
   122441599786418640, 197876884418069220, 291326565411718200,
   402790642767365580, 532269116485011360, 679761986564655540,
   845269253006298120, 1028790915809939100, 1204149805278826770,
   1393300966962369465, 1596244400860567185, 1812980106973419930,
   2043508085300927700, 2287828335843090495, 2545940858599908315,
   2817845653571381160, 3103542720757509030, 3403032060158291925,
   3716313671773729845, 4043387555603822790, 4384253711648570760,
   4738912139907973755, 5107362840382031775, 5489605813070744820,
   5885641057974112890, 6295468575092135985, 6719088364424814105,
   7156500425972147250, 7607704759734135420, 8072701365710778615,
   8551490243902076835, 9044071394308030080, 8972858242178775945,
   8482247416140035265, 8005428862315949610, 7542402580706518980,
   7093168571311743375, 6657726834131622795, 6236077369166157240,
   5828220176415346710, 5434155255879191205, 4780793647193537945,
   4497089976933892018, 4185801779428473703, 3855346910597166795,
   3536131235550081615, 3230707832717651460, 2939076702099876330,
   2661237843696756225, 2397191257508291145, 2146936943534481090,
   1910474901775326060, 1687805132230826055, 1478927634900981075,
   1283842409785791120, 1077776363386376100, 889724713348959480,
   719687459673541260, 567664602360121440, 433656141408700020,
   317662076819277000, 219682408591852380, 139717136726426160,
   77766261222998340, 33829782081568920, 7907699302137900,
   16777215]

/-- Negative-flank (rhs) recursive offsets. -/
def offtableXN24 : List ℕ :=
  [83886075, 218103795, 352321515,
   486539235, 620756955, 754974675,
   889192395, 1023410115, 1157627835,
   1291845555, 1426063275, 1543503780,
   1660944285, 1778384790, 1895825295,
   2013265800, 2130706305, 2248146810,
   2365587315, 2483027820, 2600468325,
   2717908830, 2835349335, 2868903765,
   2868903765, 2868903765, 2868903765,
   2868903765, 2868903765, 2868903765,
   2868903765, 2868903765, 2868903765,
   2868903765, 2868903765, 2868903765,
   2868903765, 2868903765, 2868903765,
   2868903765, 2868903765, 2868903765,
   2868903765, 2868903765, 2852192086,
   2852192086, 2852192086, 2801860696,
   2684420191, 2566979686, 2449539181,
   2332098676, 2214658171, 2097217666,
   1979777161, 1862336656, 1744896151,
   1627455646, 1493237926, 1359020206,
   1224802486, 1090584766, 956367046,
   822149326, 687931606, 553713886,
   419496166, 285278446, 151060726,
   65791]

def wfX24 (k : ℕ) : ℕ := wtableX24.getD k 64
def offXP24 (k : ℕ) : ℕ := offtableXP24.getD k 9115566029852934015
def offXN24 (k : ℕ) : ℕ := offtableXN24.getD k 9115566029852934015

/-- The lhs (positive-flank) parameter bundle of the fused equality. -/
def vparamsX24 : GroupedEqV.VParams where
  Nf := nfXL24T
  OFFf := offXP24
  Wf := wfX24
  Nmax := (3 * numLimbs24) * (3 * numLimbs24)
              * ((2 ^ 24 - 1) * (2 ^ 24 - 1) * (2 ^ 24 - 1))
            + numLimbs24 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24
  OFFmax := 9115566029852934015
  Wmax := 64

/-- The rhs (negative-flank) parameter bundle of the fused equality. -/
def vparamsXR24 : GroupedEqV.VParams where
  Nf := nfXR24T
  OFFf := offXN24
  Wf := wfX24
  Nmax := (3 * numLimbs24) * (3 * numLimbs24)
              * ((2 ^ 24 - 1) * (2 ^ 24 - 1) * (2 ^ 24 - 1))
            + numLimbs24 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24
  OFFmax := 9115566029852934015
  Wmax := 64

/-- Width-table entries lie in `[1, 64]`. -/
private lemma wfX24_bounds (k : ℕ) : 1 ≤ wfX24 k ∧ wfX24 k ≤ 64 := by
  unfold wfX24
  by_cases h : k < wtableX24.length
  · rw [List.getD_eq_getElem _ _ h]
    have hall : ∀ x ∈ wtableX24, 1 ≤ x ∧ x ≤ 64 := by decide
    exact hall _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨by norm_num, le_refl _⟩

set_option maxRecDepth 100000 in
/-- Tail lhs entries lie in `[1, Nmax]`. -/
private lemma nfXLtail24_bounds (x : ℕ) (hx : x ∈ nfXLtail24) :
    1 ≤ x ∧ x ≤ (3 * numLimbs24) * (3 * numLimbs24)
        * ((2 ^ 24 - 1) * (2 ^ 24 - 1) * (2 ^ 24 - 1))
      + numLimbs24 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24 := by
  have hall : ∀ y ∈ nfXLtail24, 1 ≤ y ∧ y ≤ (3 * numLimbs24) * (3 * numLimbs24)
        * ((2 ^ 24 - 1) * (2 ^ 24 - 1) * (2 ^ 24 - 1))
      + numLimbs24 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24 := by decide
  exact hall x hx

set_option maxRecDepth 100000 in
/-- Tail rhs entries lie in `[2^24, Nmax]`. -/
private lemma nfXRtail24_bounds (x : ℕ) (hx : x ∈ nfXRtail24) :
    2 ^ 24 ≤ x ∧ x ≤ (3 * numLimbs24) * (3 * numLimbs24)
        * ((2 ^ 24 - 1) * (2 ^ 24 - 1) * (2 ^ 24 - 1))
      + numLimbs24 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24 := by
  have hall : ∀ y ∈ nfXRtail24, 2 ^ 24 ≤ y ∧ y ≤ (3 * numLimbs24) * (3 * numLimbs24)
        * ((2 ^ 24 - 1) * (2 ^ 24 - 1) * (2 ^ 24 - 1))
      + numLimbs24 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24 := by decide
  exact hall x hx


set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The two-sided schedule grouping hypotheses for the fused equality
(`B = 24`, `L = 512`, `G = 72`). -/
theorem hgvx24 :
    GroupedEqXV.GVXHyps circomPrime numLimbsX24 24 gfX24 posOfX24 71 vparamsX24 vparamsXR24 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide⟩
  · intro k; simp only [posOfX24, gfX24]; split_ifs <;> omega
  · intro k; simp only [gfX24]; split_ifs <;> omega
  · intro k
    have h := wfX24_bounds k
    have hWf : vparamsX24.Wf k = wfX24 k := rfl
    rw [hWf]
    refine ⟨by omega, ?_⟩
    calc (2 : ℕ) ^ wfX24 k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) h.2
      _ < circomPrime := by decide
  · intro j
    constructor
    · show 1 ≤ nfXL24T j
      unfold nfXL24T
      by_cases hc : j < 322
      · rw [if_pos hc]; unfold nfXL24; omega
      · rw [if_neg hc]
        by_cases h2 : j - 322 < nfXLtail24.length
        · rw [List.getD_eq_getElem _ _ h2]
          exact (nfXLtail24_bounds _ (List.getElem_mem h2)).1
        · rw [List.getD_eq_default _ _ (by omega)]
    · show 1 ≤ nfXR24T j
      unfold nfXR24T
      by_cases hc : j < 322
      · rw [if_pos hc]
        unfold nfXR24
        have : (1 : ℕ) ≤ 2 ^ 24 := by norm_num
        omega
      · rw [if_neg hc]
        by_cases h2 : j - 322 < nfXRtail24.length
        · rw [List.getD_eq_getElem _ _ h2]
          have := (nfXRtail24_bounds _ (List.getElem_mem h2)).1
          omega
        · rw [List.getD_eq_default _ _ (by omega)]
          norm_num

/-- `z2` field-no-wrap bound (3m² triple-product coefficients fit the field). -/
theorem hf2X24 : (3 * numLimbs24) * (3 * numLimbs24)
    * ((2 ^ 24 - 1) * (2 ^ 24 - 1) * (2 ^ 24 - 1)) < circomPrime := by decide

/-- `z3` field-no-wrap bound (`q·n` window coefficients fit the field). -/
theorem hf3X24 : (3 * numLimbs24) * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) < circomPrime := by decide

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- LHS adequacy: the top-limb-aware triple-product cap is `< nfXL24T`. -/
theorem hlhs_adX24 : ∀ k, WindowCaps.triCapW 24 16 numLimbs24 k < vparamsX24.Nf k := by
  intro k
  show WindowCaps.triCapW 24 16 numLimbs24 k < nfXL24T k
  unfold nfXL24T
  by_cases hk : k < 322
  · rw [if_pos hk]
    have h1 : WindowCaps.triCapW 24 16 numLimbs24 k
        ≤ WindowCaps.triCap numLimbs24 k * ((2 ^ 24 - 1) * (2 ^ 24 - 1) * (2 ^ 24 - 1)) :=
      WindowCaps.triCapW_le_tri (by norm_num) (by norm_num) k (by
        show k ≤ 3 * numLimbs24 - 3
        have hnum : numLimbs24 = 171 := rfl
        omega)
    unfold nfXL24
    omega
  · rw [if_neg hk]
    by_cases hk2 : k < 512
    · rw [WindowCaps.triCapW_eqL]
      interval_cases k <;> decide
    · have hnum : numLimbs24 = 171 := rfl
      have h0 : WindowCaps.triCapW 24 16 numLimbs24 k = 0 := by
        unfold WindowCaps.triCapW WindowCaps.wconv
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [if_neg]
        rintro ⟨h1, h2⟩
        omega
      rw [h0]
      rw [List.getD_eq_default _ _ (by
        have hlen : nfXLtail24.length = 190 := rfl
        omega)]
      norm_num

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- RHS adequacy: the top-limb-aware `q·n` cap plus one `em` limb is `≤ nfXR24T`. -/
theorem hrhs_adX24 : ∀ k, WindowCaps.qnCapW 24 16 8 numLimbs24 k + 2 ^ 24 ≤ vparamsXR24.Nf k := by
  intro k
  show WindowCaps.qnCapW 24 16 8 numLimbs24 k + 2 ^ 24 ≤ nfXR24T k
  unfold nfXR24T
  by_cases hk : k < 322
  · rw [if_pos hk]
    have h1 : WindowCaps.qnCapW 24 16 8 numLimbs24 k
        ≤ WindowCaps.qnCap numLimbs24 k * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) :=
      WindowCaps.qnCapW_le_qn (by norm_num) (by norm_num) k
    unfold nfXR24
    omega
  · rw [if_neg hk]
    by_cases hk2 : k < 512
    · rw [WindowCaps.qnCapW_eqL]
      interval_cases k <;> decide
    · have hnum : numLimbs24 = 171 := rfl
      have h0 : WindowCaps.qnCapW 24 16 8 numLimbs24 k = 0 := by
        unfold WindowCaps.qnCapW WindowCaps.wconv
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [if_neg]
        rintro ⟨h1, h2⟩
        omega
      rw [h0]
      rw [List.getD_eq_default _ _ (by
        have hlen : nfXRtail24.length = 190 := rfl
        omega)]
      norm_num


/-! ## Graduated two-sided carry parameters for the quadratic squaring `GroupedEqXV` equalities

The 15 quadratic squaring batteries (`SquareModLazyGT` once, 14 more via
`ModExpSqGT`) assert `a·a = q·n + r` over `2m−1 = 341` coefficients. Replacing
the uniform-`g = 9` one-sided `GroupedEqV` (37 checked carries + a local final
row) with the two-sided variable-group `GroupedEqXV` (37 checked carries + one
`polyEval` row) saves one allocation and one constraint per battery: exact
window-sum coefficient bounds and asymmetric per-side offsets shave one bit off
the first and last checked carries (`g = 8` fringe groups). -/

/-- Per-group size schedule for the quadratic equality: two `g = 8` head
groups, 36 `g = 9` groups (positions 16..340), `g = 8` beyond. -/
def gfQ24 (k : ℕ) : ℕ := if k < 2 then 8 else if k < 38 then 9 else 8

/-- Prefix positions of `gfQ24` in closed form. -/
def posOfQ24 (k : ℕ) : ℕ :=
  if k = 0 then 0
  else if k ≤ 2 then 8 * k
  else if k ≤ 38 then 16 + 9 * (k - 2)
  else 340 + 8 * (k - 38)

/-- Exact lhs (`a·a`) coefficient bound: the top-limb-aware square window sum
plus one (`WindowCaps.sqCapW 24 16 171` in its kernel-friendly list form). -/
def nfQL24 (j : ℕ) : ℕ :=
  WindowCaps.wconvL numLimbs24 numLimbs24 (WindowCaps.limbCap 24 16 numLimbs24)
    (WindowCaps.limbCap 24 16 numLimbs24) j + 1

/-- Exact rhs (`q·n + r`) coefficient bound: the same window sum (the tight
quotient shares the 16-bit top limb) plus one tight `r`-limb on the low `m`
positions, plus one. -/
def nfQR24 (j : ℕ) : ℕ :=
  WindowCaps.wconvL numLimbs24 numLimbs24 (WindowCaps.limbCap 24 16 numLimbs24)
    (WindowCaps.limbCap 24 16 numLimbs24) j
    + (if j < numLimbs24 then WindowCaps.limbCap 24 16 numLimbs24 j else 0) + 1

/-- Per-boundary carry range-check widths for the `37` checked boundaries of
the quadratic equality (positions `8, 16, 25, …, 331`). -/
def wtableQ24 : List ℕ :=
  [28, 29, 30, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33,
   33, 33, 33, 33, 32, 32, 32, 32, 32, 32, 32, 31, 31, 31, 31, 30, 30, 29]

/-- Positive-flank (lhs) minimal recursive prefix offsets. -/
def offtableQP24 : List ℕ :=
  [134217719, 268435439, 419430374, 570425309, 721420244, 872415179,
   1023410114, 1174405049, 1325399984, 1476394919, 1627389854, 1778384789,
   1929379724, 2080374659, 2231369594, 2382364529, 2533359464, 2684354399,
   2835349334, 2718039900, 2567044965, 2416050030, 2265055095, 2114060160,
   1963065225, 1812070290, 1661075355, 1510080420, 1359085485, 1208090550,
   1057095615, 906100680, 755105745, 604110810, 453115875, 302120940,
   151126005]

/-- Negative-flank (rhs) minimal recursive prefix offsets. -/
def offtableQN24 : List ℕ :=
  [134217720, 268435440, 419430375, 570425310, 721420245, 872415180,
   1023410115, 1174405050, 1325399985, 1476394920, 1627389855, 1778384790,
   1929379725, 2080374660, 2231369595, 2382364530, 2533359465, 2684354400,
   2835349335, 2718039900, 2567044965, 2416050030, 2265055095, 2114060160,
   1963065225, 1812070290, 1661075355, 1510080420, 1359085485, 1208090550,
   1057095615, 906100680, 755105745, 604110810, 453115875, 302120940,
   151126005]

def wfQ24 (k : ℕ) : ℕ := wtableQ24.getD k 33
def offQP24 (k : ℕ) : ℕ := offtableQP24.getD k 2835349334
def offQN24 (k : ℕ) : ℕ := offtableQN24.getD k 2835349335

/-- The lhs (positive-flank) parameter bundle of the quadratic equality. -/
def vparamsQ24 : GroupedEqV.VParams where
  Nf := nfQL24
  OFFf := offQP24
  Wf := wfQ24
  Nmax := 171 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24
  OFFmax := 2835349335
  Wmax := 33

/-- The rhs (negative-flank) parameter bundle of the quadratic equality. -/
def vparamsQR24 : GroupedEqV.VParams where
  Nf := nfQR24
  OFFf := offQN24
  Wf := wfQ24
  Nmax := 171 * ((2 ^ 24 - 1) * (2 ^ 24 - 1)) + 2 ^ 24
  OFFmax := 2835349335
  Wmax := 33

/-- All quad width-table entries lie in `[28, 33]`. -/
private lemma wtableQ24_bounds (k : ℕ) : 28 ≤ wfQ24 k ∧ wfQ24 k ≤ 33 := by
  unfold wfQ24
  by_cases h : k < wtableQ24.length
  · rw [List.getD_eq_getElem _ _ h]
    have hall : ∀ x ∈ wtableQ24, 28 ≤ x ∧ x ≤ 33 := by decide
    exact hall _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨by norm_num, le_refl _⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The two-sided schedule grouping hypotheses for the quadratic squaring
equality (`B = 24`, `L = 341`, `G = 39`). -/
theorem hgvxQ24 :
    GroupedEqXV.GVXHyps circomPrime (2 * numLimbs24 - 1) 24 gfQ24 posOfQ24 39
      vparamsQ24 vparamsQR24 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide⟩
  · intro k; simp only [posOfQ24, gfQ24]; split_ifs <;> omega
  · intro k; simp only [gfQ24]; split_ifs <;> omega
  · intro k
    have h := wtableQ24_bounds k
    have hWf : vparamsQ24.Wf k = wfQ24 k := rfl
    rw [hWf]
    refine ⟨by omega, ?_⟩
    calc (2 : ℕ) ^ wfQ24 k ≤ 2 ^ 33 := Nat.pow_le_pow_right (by norm_num) h.2
      _ < circomPrime := by decide
  · intro j
    constructor
    · show 1 ≤ nfQL24 j
      unfold nfQL24
      exact Nat.le_add_left 1 _
    · show 1 ≤ nfQR24 j
      unfold nfQR24
      exact Nat.le_add_left 1 _

/-- `Nf` adequacy for the quadratic batteries (`NfOk2`): the exact window caps
sit one below the `+1` closed-form bounds. -/
theorem hNfQ24 :
    SquareModLazyGT.NfOk2 (m := numLimbs24) 24 16 vparamsQ24 vparamsQR24 := by
  constructor
  · intro j hj
    show WindowCaps.sqCapW 24 16 numLimbs24 j < nfQL24 j
    rw [WindowCaps.sqCapW_eqL]
    unfold nfQL24
    omega
  · intro j hj
    show WindowCaps.wconv numLimbs24 numLimbs24 (WindowCaps.limbCap 24 16 numLimbs24)
          (WindowCaps.limbCap 24 16 numLimbs24) j
        + (if j < numLimbs24 then WindowCaps.limbCap 24 16 numLimbs24 j else 0) < nfQR24 j
    rw [WindowCaps.wconv_eq_wconvL]
    unfold nfQR24
    exact Nat.lt_succ_self _



/-! ## Balanced fused-final `GroupedEqD` params (phase 3)

The fused triple-product equality over `3m−1 = 512` coefficients with a balanced
input `a = r_15`: the lhs `z2 = (aS·aS)·b` coefficients are *signed*
(`|·| ≤ a2cap`), the rhs is `q·n + em` unsigned. Two-sided windows via
`GroupedEqD`; the positive flank `NfP = a2cap + 1`, the negative flank
`NfN = a2cap + qnCap + em + 1`. Cap lists are precomputed so the `GVXHyps`
`decide` and the adequacy extractions only touch bignum arithmetic. -/

def sqBListF : List ℕ := [70368744177664, 140737488355328, 211106232532992, 281474976710656, 351843720888320, 422212465065984, 492581209243648, 562949953421312, 633318697598976, 703687441776640, 774056185954304, 844424930131968, 914793674309632, 985162418487296, 1055531162664960, 1125899906842624, 1196268651020288, 1266637395197952, 1337006139375616, 1407374883553280, 1477743627730944, 1548112371908608, 1618481116086272, 1688849860263936, 1759218604441600, 1829587348619264, 1899956092796928, 1970324836974592, 2040693581152256, 2111062325329920, 2181431069507584, 2251799813685248, 2322168557862912, 2392537302040576, 2462906046218240, 2533274790395904, 2603643534573568, 2674012278751232, 2744381022928896, 2814749767106560, 2885118511284224, 2955487255461888, 3025855999639552, 3096224743817216, 3166593487994880, 3236962232172544, 3307330976350208, 3377699720527872, 3448068464705536, 3518437208883200, 3588805953060864, 3659174697238528, 3729543441416192, 3799912185593856, 3870280929771520, 3940649673949184, 4011018418126848, 4081387162304512, 4151755906482176, 4222124650659840, 4292493394837504, 4362862139015168, 4433230883192832, 4503599627370496, 4573968371548160, 4644337115725824, 4714705859903488, 4785074604081152, 4855443348258816, 4925812092436480, 4996180836614144, 5066549580791808, 5136918324969472, 5207287069147136, 5277655813324800, 5348024557502464, 5418393301680128, 5488762045857792, 5559130790035456, 5629499534213120, 5699868278390784, 5770237022568448, 5840605766746112, 5910974510923776, 5981343255101440, 6051711999279104, 6122080743456768, 6192449487634432, 6262818231812096, 6333186975989760, 6403555720167424, 6473924464345088, 6544293208522752, 6614661952700416, 6685030696878080, 6755399441055744, 6825768185233408, 6896136929411072, 6966505673588736, 7036874417766400, 7107243161944064, 7177611906121728, 7247980650299392, 7318349394477056, 7388718138654720, 7459086882832384, 7529455627010048, 7599824371187712, 7670193115365376, 7740561859543040, 7810930603720704, 7881299347898368, 7951668092076032, 8022036836253696, 8092405580431360, 8162774324609024, 8233143068786688, 8303511812964352, 8373880557142016, 8444249301319680, 8514618045497344, 8584986789675008, 8655355533852672, 8725724278030336, 8796093022208000, 8866461766385664, 8936830510563328, 9007199254740992, 9077567998918656, 9147936743096320, 9218305487273984, 9288674231451648, 9359042975629312, 9429411719806976, 9499780463984640, 9570149208162304, 9640517952339968, 9710886696517632, 9781255440695296, 9851624184872960, 9921992929050624, 9992361673228288, 10062730417405952, 10133099161583616, 10203467905761280, 10273836649938944, 10344205394116608, 10414574138294272, 10484942882471936, 10555311626649600, 10625680370827264, 10696049115004928, 10766417859182592, 10836786603360256, 10907155347537920, 10977524091715584, 11047892835893248, 11118261580070912, 11188630324248576, 11258999068426240, 11329367812603904, 11399736556781568, 11470105300959232, 11540474045136896, 11610842789314560, 11681211533492224, 11751580277669888, 11821949021847552, 11892317766025216, 11962686510202880, 11894516772503552, 11824148028325888, 11753779284148224, 11683410539970560, 11613041795792896, 11542673051615232, 11472304307437568, 11401935563259904, 11331566819082240, 11261198074904576, 11190829330726912, 11120460586549248, 11050091842371584, 10979723098193920, 10909354354016256, 10838985609838592, 10768616865660928, 10698248121483264, 10627879377305600, 10557510633127936, 10487141888950272, 10416773144772608, 10346404400594944, 10276035656417280, 10205666912239616, 10135298168061952, 10064929423884288, 9994560679706624, 9924191935528960, 9853823191351296, 9783454447173632, 9713085702995968, 9642716958818304, 9572348214640640, 9501979470462976, 9431610726285312, 9361241982107648, 9290873237929984, 9220504493752320, 9150135749574656, 9079767005396992, 9009398261219328, 8939029517041664, 8868660772864000, 8798292028686336, 8727923284508672, 8657554540331008, 8587185796153344, 8516817051975680, 8446448307798016, 8376079563620352, 8305710819442688, 8235342075265024, 8164973331087360, 8094604586909696, 8024235842732032, 7953867098554368, 7883498354376704, 7813129610199040, 7742760866021376, 7672392121843712, 7602023377666048, 7531654633488384, 7461285889310720, 7390917145133056, 7320548400955392, 7250179656777728, 7179810912600064, 7109442168422400, 7039073424244736, 6968704680067072, 6898335935889408, 6827967191711744, 6757598447534080, 6687229703356416, 6616860959178752, 6546492215001088, 6476123470823424, 6405754726645760, 6335385982468096, 6265017238290432, 6194648494112768, 6124279749935104, 6053911005757440, 5983542261579776, 5913173517402112, 5842804773224448, 5772436029046784, 5702067284869120, 5631698540691456, 5561329796513792, 5490961052336128, 5420592308158464, 5350223563980800, 5279854819803136, 5209486075625472, 5139117331447808, 5068748587270144, 4998379843092480, 4928011098914816, 4857642354737152, 4787273610559488, 4716904866381824, 4646536122204160, 4576167378026496, 4505798633848832, 4435429889671168, 4365061145493504, 4294692401315840, 4224323657138176, 4153954912960512, 4083586168782848, 4013217424605184, 3942848680427520, 3872479936249856, 3802111192072192, 3731742447894528, 3661373703716864, 3591004959539200, 3520636215361536, 3450267471183872, 3379898727006208, 3309529982828544, 3239161238650880, 3168792494473216, 3098423750295552, 3028055006117888, 2957686261940224, 2887317517762560, 2816948773584896, 2746580029407232, 2676211285229568, 2605842541051904, 2535473796874240, 2465105052696576, 2394736308518912, 2324367564341248, 2253998820163584, 2183630075985920, 2113261331808256, 2042892587630592, 1972523843452928, 1902155099275264, 1831786355097600, 1761417610919936, 1691048866742272, 1620680122564608, 1550311378386944, 1479942634209280, 1409573890031616, 1339205145853952, 1268836401676288, 1198467657498624, 1128098913320960, 1057730169143296, 987361424965632, 916992680787968, 846623936610304, 776255192432640, 705886448254976, 635517704077312, 565148959899648, 494780215721984, 424411471544320, 354042727366656, 283673983188992, 213305239011328, 142936494833664, 72567750656000, 2199006478336, 17179607041]

def a2ListF : List ℕ := [1180591550348667125760, 3541774651046001377280, 7083549302092002754560, 11805915503486671257600, 17708873255230006886400, 24792422557322009640960, 33056563409762679521280, 42501295812552016527360, 53126619765690020659200, 64932535269176691916800, 77919042323012030300160, 92086140927196035809280, 107433831081728708444160, 123962112786610048204800, 141670986041840055091200, 160560450847418729103360, 180630507203346070241280, 201881155109622078504960, 224312394566246753894400, 247924225573220096409600, 272716648130542106050560, 298689662238212782817280, 325843267896232126709760, 354177465104600137728000, 383692253863316815872000, 414387634172382161141760, 446263606031796173537280, 479320169441558853058560, 513557324401670199705600, 548975070912130213478400, 585573408972938894376960, 623352338584096242401280, 662311859745602257551360, 702451972457456939827200, 743772676719660289228800, 786273972532212305756160, 829955859895112989409280, 874818338808362340188160, 920861409271960358092800, 968085071285907043123200, 1016489324850202395279360, 1066074169964846414561280, 1116839606629839100968960, 1168785634845180454502400, 1221912254610870475161600, 1276219465926909162946560, 1331707268793296517857280, 1388375663210032539893760, 1446224649177117229056000, 1505254226694550585344000, 1565464395762332608757760, 1626855156380463299297280, 1689426508548942656962560, 1753178452267770681753600, 1818110987536947373670400, 1884224114356472732712960, 1951517832726346758881280, 2019992142646569452175360, 2089647044117140812595200, 2160482537138060840140800, 2232498621709329534812160, 2305695297830946896609280, 2380072565502912925532160, 2455630424725227621580800, 2532368875497890984755200, 2610287917820903015055360, 2689387551694263712481280, 2769667777117973077032960, 2851128594092031108710400, 2933770002616437807513600, 3017592002691193173442560, 3102594594316297206497280, 3188777777491749906677760, 3276141552217551273984000, 3364685918493701308416000, 3454410876320200009973760, 3545316425697047378657280, 3637402566624243414466560, 3730669299101788117401600, 3825116623129681487462400, 3920744538707923524648960, 4017553045836514228961280, 4115542144515453600399360, 4214711834744741638963200, 4315062116524378344652800, 4416592989854363717468160, 4519304454734697757409280, 4623196511165380464476160, 4728269159146411838668800, 4834522398677791879987200, 4941956229759520588431360, 5050570652391597964001280, 5160365666574024006696960, 5271341272306798716518400, 5383497469589922093465600, 5496834258423394137538560, 5611351638807214848737280, 5727049610741384227061760, 5843928174225902272512000, 5961987329260768985088000, 6081227075845984364789760, 6201647413981548411617280, 6323248343667461125570560, 6446029864903722506649600, 6569991977690332554854400, 6695134682027291270184960, 6821457977914598652641280, 6948961865352254702223360, 7077646344340259418931200, 7207511414878612802764800, 7338557076967314853724160, 7470783330606365571809280, 7604190175795764957020160, 7738777612535513009356800, 7874545640825609728819200, 8011494260666055115407360, 8149623472056849169121280, 8288933274997991889960960, 8429423669489483277926400, 8571094655531323333017600, 8713946233123512055234560, 8857978402266049444577280, 9003191162958935501045760, 9149584515202170224640000, 9297158458995753615360000, 9445912994339685673205760, 9595848121233966398177280, 9746963839678595790274560, 9899260149673573849497600, 10052737051218900575846400, 10207394544314575969320960, 10363232628960600029921280, 10520251305156972757647360, 10678450572903694152499200, 10837830432200764214476800, 10998390883048182943580160, 11160131925445950339809280, 11323053559394066403164160, 11487155784892531133644800, 11652438601941344531251200, 11818902010540506595983360, 11986546010690017327841280, 12155370602389876726824960, 12325375785640084792934400, 12496561560440641526169600, 12668927926791546926530560, 12842474884692800994017280, 13017202434144403728629760, 13193110575146355130368000, 13370199307698655199232000, 13548468631801303935221760, 13727918547454301338337280, 13908549054657647408578560, 14090360153411342145945600, 14273351843715385550438400, 14457524125569777622056960, 14642876998974518360801280, 14829410463929607766671360, 15017124520435045839667200, 15206019168490832579788800, 15396094408096967987036160, 15587350239253452061409280, 15779786661960284802908160, 15973403676217466211532800, 16168201282024996287283200, 16364179479382875030159360, 16561338268291102440161280, 16759677648749678517288960, 16959197620758603261542400, 17159898184317876672921600, 17358279069596575869173760, 17554298771774577731174400, 17747957290851882258923520, 17939254626828489452421120, 18128190779704399311667200, 18314765749479611836661760, 18498979536154127027404800, 18680832139727944883896320, 18860323560201065406136320, 19037453797573488594124800, 19212222851845214447861760, 19384630723016242967347200, 19554677411086574152581120, 19722362916056208003563520, 19887687237925144520294400, 20050650376693383702773760, 20211252332360925551001600, 20369493104927770064977920, 20525372694393917244702720, 20678891100759367090176000, 20830048324024119601397760, 20978844364188174778368000, 21125279221251532621086720, 21269352895214193129553920, 21411065386076156303769600, 21550416693837422143733760, 21687406818497990649446400, 21822035760057861820907520, 21954303518517035658117120, 22084210093875512161075200, 22211755486133291329781760, 22336939695290373164236800, 22459762721346757664440320, 22580224564302444830392320, 22698325224157434662092800, 22814064700911727159541760, 22927442994565322322739200, 23038460105118220151685120, 23147116032570420646379520, 23253410776921923806822400, 23357344338172729633013760, 23458916716322838124953600, 23558127911372249282641920, 23654977923320963106078720, 23749466752168979595264000, 23841594397916298750197760, 23931360860562920570880000, 24018766140108845057310720, 24103810236554072209489920, 24186493149898602027417600, 24266814880142434511093760, 24344775427285569660518400, 24420374791328007475691520, 24493612972269747956613120, 24564489970110791103283200, 24633005784851136915701760, 24699160416490785393868800, 24762953865029736537784320, 24824386130467990347448320, 24883457212805546822860800, 24940167112042405964021760, 24994515828178567770931200, 25046503361214032243589120, 25096129711148799381995520, 25143394877982869186150400, 25188298861716241656053760, 25230841662348916791705600, 25271023279880894593105920, 25308843714312175060254720, 25344302965642758193152000, 25377401033872643991797760, 25408137919001832456192000, 25436513621030323586334720, 25462528139958117382225920, 25486181475785213843865600, 25507473628511612971253760, 25526404598137314764390400, 25542974384662319223275520, 25557182988086626347909120, 25569030408410236138291200, 25578516645633148594421760, 25585641699755363716300800, 25590405570776881503928320, 25592808258697701957304320, 25592849763517825076428800, 25590530085237250861301760, 25585849223855979311923200, 25578807179374010428293120, 25569403951791344210411520, 25557639541107980658278400, 25543513947323919771893760, 25527027170439161551257600, 25508179210453705996369920, 25486970067367553107230720, 25463399741180702883840000, 25437468231893155326197760, 25409175539504910434304000, 25378521664015968208158720, 25345506605426328647761920, 25310130363735991753113600, 25272392938944957524213760, 25232294331053225961062400, 25189834540060797063659520, 25145013565967670832005120, 25097831408773847266099200, 25048288068479326365941760, 24996383545084108131532800, 24942117838588192562872320, 24885490948991579659960320, 24826502876294269422796800, 24765153620496261851381760, 24701443181597556945715200, 24635371559598154705797120, 24566938754498055131627520, 24496144766297258223206400, 24422989594995763980533760, 24347473240593572403609600, 24269595703090683492433920, 24189356982487097247006720, 24106757078782813667328000, 24021795991977832753397760, 23934473722072154505216000, 23844790269065778922782720, 23752745632958706006097920, 23658339813750935755161600, 23561572811442468169973760, 23462444626033303250534400, 23360955257523440996843520, 23257104705912881408901120, 23150892971201624486707200, 23042320053389670230261760, 22931385952477018639564800, 22818090668463669714616320, 22702434201349623455416320, 22584416551134879861964800, 22464037717819438934261760, 22341297701403300672307200, 22216196501886465076101120, 22088734119268932145643520, 21958910553550701880934400, 21826725804731774281973760, 21692179872812149348761600, 21555272757791827081297920, 21416004459670807479582720, 21274374978449090543616000, 21130384314126676273397760, 20984032466703564668928000, 20835319436179755730206720, 20684245222555249457233920, 20530809825830045850009600, 20375013246004144908533760, 20216855483077546632806400, 20056336537050251022827520, 19893456407922258078597120, 19728215095693567800115200, 19560612600364180187381760, 19390648921934095240396800, 19218324060403312959160320, 19043638015771833343672320, 18866590788039656393932800, 18687182377206782109941760, 18505412783273210491699200, 18321282006238941539205120, 18134790046103975252459520, 17945936902868311631462400, 17754722576531950676213760, 17561147067094892386713600, 17365210374557136762961920, 17166912498918683804958720, 16966253440179533512704000, 16766692395688336149446655, 16568311510409636953194495, 16371111216681286424068095, 16175091514503284562067455, 15980252403875631367192575, 15786593884798326839443455, 15594115957271370978820095, 15402818621294763785322495, 15212701876868505258950655, 15023765723992595399704575, 14836010162667034207584255, 14649435192891821682589695, 14464040814666957824720895, 14279827027992442633977855, 14096793832868276110360575, 13914941229294458253869055, 13734269217270989064503295, 13554777796797868542263295, 13376466967875096687149055, 13199336730502673499160575, 13023387084680598978297855, 12848618030408873124560895, 12675029567687495937949695, 12502621696516467418464255, 12331394416895787566104575, 12161347728825456380870655, 11992481632305473862762495, 11824796127335840011780095, 11658291213916554827923455, 11492966892047618311192575, 11328823161729030461587455, 11165860022960791279108095, 11004077475742900763754495, 10843475520075358915526655, 10684054155958165734424575, 10525813383391321220448255, 10368753202374825373597695, 10212873612908678193872895, 10058174614992879681273855, 9904656208627429835800575, 9752318393812328657453055, 9601161170547576146231295, 9451184538833172302135295, 9302388498669117125165055, 9154773050055410615320575, 9008338192992052772601855, 8863083927479043597008895, 8719010253516383088541695, 8576117171104071247200255, 8434404680242108072984575, 8293872780930493565894655, 8154521473169227725930495, 8016350756958310553092095, 7879360632297742047379455, 7743551099187522208792575, 7608922157627651037331455, 7475473807618128532996095, 7343206049158954695786495, 7212118882250129525702655, 7082212306891653022744575, 6953486323083525186912255, 6825940930825746018205695, 6699576130118315516624895, 6574391920961233682169855, 6450388303354500514840575, 6327565277298116014637055, 6205922842792080181559295, 6085460999836393015607295, 5966179748431054516781055, 5848079088576064685080575, 5731159020271423520505855, 5615419543517131023056895, 5500860658313187192733695, 5387482364659592029536255, 5275284662556345533464575, 5164267552003447704518655, 5054431033000898542698495, 4945775105548698048004095, 4838299769646846220435455, 4732005025295343059992575, 4626890872494188566675455, 4522957311243382740484095, 4420204341542925581418495, 4318631963392817089478655, 4218240176793057264664575, 4119028981743646106976255, 4020998378244583616413695, 3924148366295869792976895, 3828478945897504636665855, 3733990117049488147480575, 3640681879751820325421055, 3548554234004501170487295, 3457607179807530682679295, 3367840717160908861997055, 3279254846064635708440575, 3191849566518711222009855, 3105624878523135402704895, 3020580782077908250525695, 2936717277183029765472255, 2854034363838499947544575, 2772532042044318796742655, 2692210311800486313066495, 2613069173107002496516095, 2535108625963867347091455, 2458328670371080864792575, 2382729306328643049619455, 2308310533836553901572095, 2235072352894813420650495, 2163014763503421606854655, 2092137765662378460184575, 2022441359371683980640255, 1953925544631338168221695, 1886590321441341022928895, 1820435689801692544761855, 1755461649712392733720575, 1691668201173441589805055, 1629055344184839113015295, 1567623078746585303351295, 1507371404858680160813055, 1448300322521123685400575, 1390409831733915877113855, 1333699932497056735952895, 1278170624810546261917695, 1223821908674384455008255, 1170653784088571315224575, 1118666251053106842566655, 1067859309567991037034495, 1018232959633223898628095, 969787201248805427347455, 922522034414735623192575, 876437459131014486163455, 831533475397642016260095, 787810083214618213482495, 745267282581943077830655, 703905073499616609304575, 663723455967638807904255, 624722429986009673629695, 586901995554729206480895, 550262152673797406457855, 514802901343214273560575, 480524241562979807789055, 447426173333094009143295, 415508696653556877623295, 384771811524368413229055, 355215517945528615960575, 326839815917037485817855, 299644705438895022800895, 273630186511101226909695, 248796259133656098144255, 225142923306559636504575, 202670179029811841990655, 181378026303412714602495, 161266465127362254340095, 142335495501660461203455, 124585117426307335192575, 108015330901302876307455, 92626135926647084548095, 78417532502339959914495, 65389520628381502406655, 53542100304771712024575, 42875271531510588768255, 33389034308598132637695, 25083388636034343632895, 17958334513819221753855, 12013871941952767000575, 7250000920434979373055, 3666721449265858871295, 1264033528445405495295, 41937157973619245055, 432337850500120575, 1125865547431935, 0]

def q2ListF : List ℕ := [281474943156225, 562949886312450, 844424829468675, 1125899772624900, 1407374715781125, 1688849658937350, 1970324602093575, 2251799545249800, 2533274488406025, 2814749431562250, 3096224374718475, 3377699317874700, 3659174261030925, 3940649204187150, 4222124147343375, 4503599090499600, 4785074033655825, 5066548976812050, 5348023919968275, 5629498863124500, 5910973806280725, 6192448749436950, 6473923692593175, 6755398635749400, 7036873578905625, 7318348522061850, 7599823465218075, 7881298408374300, 8162773351530525, 8444248294686750, 8725723237842975, 9007198180999200, 9288673124155425, 9570148067311650, 9851623010467875, 10133097953624100, 10414572896780325, 10696047839936550, 10977522783092775, 11258997726249000, 11540472669405225, 11821947612561450, 12103422555717675, 12384897498873900, 12666372442030125, 12947847385186350, 13229322328342575, 13510797271498800, 13792272214655025, 14073747157811250, 14355222100967475, 14636697044123700, 14918171987279925, 15199646930436150, 15481121873592375, 15762596816748600, 16044071759904825, 16325546703061050, 16607021646217275, 16888496589373500, 17169971532529725, 17451446475685950, 17732921418842175, 18014396361998400, 18295871305154625, 18577346248310850, 18858821191467075, 19140296134623300, 19421771077779525, 19703246020935750, 19984720964091975, 20266195907248200, 20547670850404425, 20829145793560650, 21110620736716875, 21392095679873100, 21673570623029325, 21955045566185550, 22236520509341775, 22517995452498000, 22799470395654225, 23080945338810450, 23362420281966675, 23643895225122900, 23925370168279125, 24206845111435350, 24488320054591575, 24769794997747800, 25051269940904025, 25332744884060250, 25614219827216475, 25895694770372700, 26177169713528925, 26458644656685150, 26740119599841375, 27021594542997600, 27303069486153825, 27584544429310050, 27866019372466275, 28147494315622500, 28428969258778725, 28710444201934950, 28991919145091175, 29273394088247400, 29554869031403625, 29836343974559850, 30117818917716075, 30399293860872300, 30680768804028525, 30962243747184750, 31243718690340975, 31525193633497200, 31806668576653425, 32088143519809650, 32369618462965875, 32651093406122100, 32932568349278325, 33214043292434550, 33495518235590775, 33776993178747000, 34058468121903225, 34339943065059450, 34621418008215675, 34902892951371900, 35184367894528125, 35465842837684350, 35747317780840575, 36028792723996800, 36310267667153025, 36591742610309250, 36873217553465475, 37154692496621700, 37436167439777925, 37717642382934150, 37999117326090375, 38280592269246600, 38562067212402825, 38843542155559050, 39125017098715275, 39406492041871500, 39687966985027725, 39969441928183950, 40250916871340175, 40532391814496400, 40813866757652625, 41095341700808850, 41376816643965075, 41658291587121300, 41939766530277525, 42221241473433750, 42502716416589975, 42784191359746200, 43065666302902425, 43347141246058650, 43628616189214875, 43910091132371100, 44191566075527325, 44473041018683550, 44754515961839775, 45035990904996000, 45317465848152225, 45598940791308450, 45880415734464675, 46161890677620900, 46443365620777125, 46724840563933350, 47006315507089575, 47287790450245800, 47569265393402025, 47850740336558250, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47851839831343275, 47570369166376875, 47288894223220650, 47007419280064425, 46725944336908200, 46444469393751975, 46162994450595750, 45881519507439525, 45600044564283300, 45318569621127075, 45037094677970850, 44755619734814625, 44474144791658400, 44192669848502175, 43911194905345950, 43629719962189725, 43348245019033500, 43066770075877275, 42785295132721050, 42503820189564825, 42222345246408600, 41940870303252375, 41659395360096150, 41377920416939925, 41096445473783700, 40814970530627475, 40533495587471250, 40252020644315025, 39970545701158800, 39689070758002575, 39407595814846350, 39126120871690125, 38844645928533900, 38563170985377675, 38281696042221450, 38000221099065225, 37718746155909000, 37437271212752775, 37155796269596550, 36874321326440325, 36592846383284100, 36311371440127875, 36029896496971650, 35748421553815425, 35466946610659200, 35185471667502975, 34903996724346750, 34622521781190525, 34341046838034300, 34059571894878075, 33778096951721850, 33496622008565625, 33215147065409400, 32933672122253175, 32652197179096950, 32370722235940725, 32089247292784500, 31807772349628275, 31526297406472050, 31244822463315825, 30963347520159600, 30681872577003375, 30400397633847150, 30118922690690925, 29837447747534700, 29555972804378475, 29274497861222250, 28993022918066025, 28711547974909800, 28430073031753575, 28148598088597350, 27867123145441125, 27585648202284900, 27304173259128675, 27022698315972450, 26741223372816225, 26459748429660000, 26178273486503775, 25896798543347550, 25615323600191325, 25333848657035100, 25052373713878875, 24770898770722650, 24489423827566425, 24207948884410200, 23926473941253975, 23644998998097750, 23363524054941525, 23082049111785300, 22800574168629075, 22519099225472850, 22237624282316625, 21956149339160400, 21674674396004175, 21393199452847950, 21111724509691725, 20830249566535500, 20548774623379275, 20267299680223050, 19985824737066825, 19704349793910600, 19422874850754375, 19141399907598150, 18859924964441925, 18578450021285700, 18296975078129475, 18015500134973250, 17734025191817025, 17452550248660800, 17171075305504575, 16889600362348350, 16608125419192125, 16326650476035900, 16045175532879675, 15763700589723450, 15482225646567225, 15200750703411000, 14919275760254775, 14637800817098550, 14356325873942325, 14074850930786100, 13793375987629875, 13511901044473650, 13230426101317425, 12948951158161200, 12667476215004975, 12386001271848750, 12104526328692525, 11823051385536300, 11541576442380075, 11260101499223850, 10978626556067625, 10697151612911400, 10415676669755175, 10134201726598950, 9852726783442725, 9571251840286500, 9289776897130275, 9008301953974050, 8726827010817825, 8445352067661600, 8163877124505375, 7882402181349150, 7600927238192925, 7319452295036700, 7037977351880475, 6756502408724250, 6475027465568025, 6193552522411800, 5912077579255575, 5630602636099350, 5349127692943125, 5067652749786900, 4786177806630675, 4504702863474450, 4223227920318225, 3941752977162000, 3660278034005775, 3378803090849550, 3097328147693325, 2815853204537100, 2534378261380875, 2252903318224650, 1971428375068425, 1689953431912200, 1408478488755975, 1127003545599750, 845528602443525, 564053659287300, 282578716131075, 1103772974850, 16711425]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem sqBListF_ok : (List.range (2 * numLimbs24 - 1)).all
    (fun k => WindowCaps.wconvL numLimbs24 numLimbs24
      (WindowCaps.balCap 24 17 numLimbs24) (WindowCaps.balCap 24 17 numLimbs24) k
        == sqBListF.getD k 0) = true := by decide

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem a2ListF_ok : (List.range (3 * numLimbs24 - 1)).all
    (fun k => WindowCaps.wconvL (2 * numLimbs24 - 1) numLimbs24
      (fun i => sqBListF.getD i 0) (WindowCaps.limbCap 24 16 numLimbs24) k
        == a2ListF.getD k 0) = true := by decide

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem q2ListF_ok : (List.range (3 * numLimbs24 - 1)).all
    (fun k => WindowCaps.qnCapW 24 16 8 numLimbs24 k == q2ListF.getD k 0) = true := by decide

/-- Group-size schedule for the balanced fused equality (`G = 70`). -/
def gfXbal (k : ℕ) : ℕ := if k = 0 then 2 else if k < 16 then 8 else if k < 52 then 7 else 8

/-- Prefix positions of `gfXbal` in closed form. -/
def posOfXbal (k : ℕ) : ℕ :=
  if k = 0 then 0
  else if k ≤ 16 then 2 + 8 * (k - 1)
  else if k ≤ 52 then 122 + 7 * (k - 16)
  else 374 + 8 * (k - 52)

/-- Positive-flank (lhs) `NfP = a2cap + 1`. -/
def nfPbalF (k : ℕ) : ℕ := a2ListF.getD k 0 + 1

/-- Negative-flank (rhs) `NfN = a2cap + qnCap + em + 1`. -/
def nfNbalF (k : ℕ) : ℕ :=
  a2ListF.getD k 0 + q2ListF.getD k 0
    + (if k < numLimbs24 then WindowCaps.limbCap 24 16 numLimbs24 k else 0) + 1

def wtableXbal : List ℕ := [49, 53, 55, 56, 57, 57, 58, 58, 59, 59, 59, 59, 60, 60, 60, 60, 61, 61, 61, 61, 61, 61, 61, 61, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 61, 61, 61, 61, 61, 61, 61, 60, 60, 60, 60, 60, 59, 59, 59, 58, 58, 58, 57, 56, 56, 54, 52]
def offtableXPbal : List ℕ := [211106224144383, 3870280887828477, 12033055178883067, 24699429097308153, 41869402643103735, 63542975816269813, 89720148616806387, 120400921044713457, 155585293099991023, 195273264782639085, 239464836092657643, 288160007030046697, 341358777594806247, 399061147786936293, 461267117606436835, 527976687053307873, 590041919388647391, 655555220188692446, 724516589453443036, 796926027182899162, 872783533377060824, 952089108035928023, 1034634118819610582, 1113464429518766040, 1185398603288510426, 1250436640128843739, 1308578540039765981, 1359824303021277151, 1404173929073377249, 1441627418196066274, 1472184770389344228, 1495845985653211110, 1512611063987666920, 1522480005392711657, 1525452809868345323, 1521529477414567917, 1510710008031379439, 1492994401718779888, 1468382658476769266, 1436874778305347572, 1398470761204514806, 1353170607174270967, 1300974316214616057, 1241881888325550075, 1175893323507073021, 1103008621759184894, 1023227783081885696, 940954377490022913, 862124066820227585, 786741824615137793, 714807650874753537, 646321545599074817, 572273835648958977, 502729725326213633, 437689214630838785, 377152303562834433, 321118992122200577, 269589280308937217, 222563168123044353, 180040655564521985, 142021742633370113, 108506429329588737, 79494715653177857, 54986601604137473, 34982087182467585, 19481172388168193, 8483857221239297, 1990141681680897]
def offtableXNbal : List ℕ := [211106257698813, 3870281055600627, 12033055480872937, 24699429533515743, 41869403213529045, 63542976520912843, 89720149455667137, 120400922017791927, 155585294207287213, 195273266024152995, 239464837468389273, 288160008539996047, 341358779238973317, 399061149565321083, 461267119519039345, 527976689100128103, 590041921552908126, 655555222470393686, 724516591852584781, 796926029699481412, 872783536011083579, 952089110787391283, 1034634121671802667, 1113464432370958125, 1185398606140702511, 1250436642981035824, 1308578542891958066, 1359824305873469236, 1404173931925569334, 1441627421048258359, 1472184773241536313, 1495845988505403195, 1512611066839859005, 1522480008244903742, 1525452812720537408, 1521529480266760002, 1510710010883571524, 1492994404570971973, 1468382661328961351, 1436874781157539657, 1398470764056706891, 1353170610026463052, 1300974319066808142, 1241881891177742160, 1175893326359265106, 1103008624611376979, 1023227785934077781, 940954380258329179, 862124069471093346, 786741827148563049, 714807653290738288, 646321547897619063, 572273837813285503, 502729727356322439, 437689216526729871, 377152305324507799, 321118993749656223, 269589281802175143, 222563169482064559, 180040656789324471, 142021743723954879, 108506430285955783, 79494716475327183, 54986602292069079, 34982087736181471, 19481172807664359, 8483857506517743, 1990141832741623]

def wfXbal (k : ℕ) : ℕ := wtableXbal.getD k 36
def offXPbal (k : ℕ) : ℕ := offtableXPbal.getD k 25769492992
def offXNbal (k : ℕ) : ℕ := offtableXNbal.getD k 25786335998

/-- The lhs (positive-flank) parameter bundle of the balanced fused equality. -/
def vparamsXbal : GroupedEqV.VParams where
  Nf := nfPbalF
  OFFf := offXPbal
  Wf := wfXbal
  Nmax := 0
  OFFmax := 0
  Wmax := 64

/-- The rhs (negative-flank) parameter bundle of the balanced fused equality. -/
def vparamsXRbal : GroupedEqV.VParams where
  Nf := nfNbalF
  OFFf := offXNbal
  Wf := wfXbal
  Nmax := 0
  OFFmax := 0
  Wmax := 64

private lemma wfXbal_bounds (k : ℕ) : 1 ≤ wfXbal k ∧ wfXbal k ≤ 64 := by
  unfold wfXbal
  by_cases h : k < wtableXbal.length
  · rw [List.getD_eq_getElem _ _ h]
    have hall : ∀ x ∈ wtableXbal, 1 ≤ x ∧ x ≤ 64 := by decide
    exact hall _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨by norm_num, by norm_num⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- `GVXHyps` for the balanced fused equality (list-based `Nf`; `decide`-checked). -/
theorem hgvxbal :
    GroupedEqXV.GVXHyps circomPrime numLimbsX24 24 gfXbal posOfXbal 70 vparamsXbal vparamsXRbal := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide⟩
  · intro k; simp only [posOfXbal, gfXbal]; split_ifs <;> omega
  · intro k; simp only [gfXbal]; split_ifs <;> omega
  · intro k
    have h := wfXbal_bounds k
    have hWf : vparamsXbal.Wf k = wfXbal k := rfl
    rw [hWf]
    refine ⟨by omega, ?_⟩
    calc (2 : ℕ) ^ wfXbal k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) h.2
      _ < circomPrime := by decide
  · intro j
    refine ⟨?_, ?_⟩
    · show 1 ≤ nfPbalF j; unfold nfPbalF; omega
    · show 1 ≤ nfNbalF j; unfold nfNbalF; omega

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- The `GVDHyps` window leg: `NfP + NfN ≤ p` everywhere (`decide`). -/
theorem hgvdbal_window :
    ∀ j, j < numLimbsX24 → vparamsXbal.Nf j + vparamsXRbal.Nf j ≤ circomPrime := by
  have h : (List.range numLimbsX24).all (fun j => nfPbalF j + nfNbalF j ≤ circomPrime) = true := by
    decide
  rw [List.all_eq_true] at h
  intro j hj
  have := h j (List.mem_range.mpr hj)
  simpa using this

/-- `GVDHyps` for the balanced fused equality. -/
theorem hgvdbal :
    GroupedEqD.GVDHyps circomPrime numLimbsX24 24 gfXbal posOfXbal 70 vparamsXbal vparamsXRbal :=
  ⟨hgvxbal, hgvdbal_window⟩

/-- Extraction: the balanced square cap equals its precomputed list. -/
private lemma sqBcap_eq (k : ℕ) (hk : k < 2 * numLimbs24 - 1) :
    WindowCaps.wconv numLimbs24 numLimbs24
      (WindowCaps.balCap 24 17 numLimbs24) (WindowCaps.balCap 24 17 numLimbs24) k
      = sqBListF.getD k 0 := by
  have h := sqBListF_ok
  rw [List.all_eq_true] at h
  have hk' := h k (List.mem_range.mpr hk)
  rw [WindowCaps.wconv_eq_wconvL]
  exact (beq_iff_eq).mp (by simpa using hk')

set_option maxRecDepth 100000 in
/-- Extraction: the balanced triple-product cap equals `a2ListF`. -/
private lemma a2cap_eq (k : ℕ) (hk : k < 3 * numLimbs24 - 1) :
    WindowCaps.wconv (2 * numLimbs24 - 1) numLimbs24
      (WindowCaps.wconv numLimbs24 numLimbs24
        (WindowCaps.balCap 24 17 numLimbs24) (WindowCaps.balCap 24 17 numLimbs24))
      (WindowCaps.limbCap 24 16 numLimbs24) k
      = a2ListF.getD k 0 := by
  have hcongr : WindowCaps.wconv (2 * numLimbs24 - 1) numLimbs24
      (WindowCaps.wconv numLimbs24 numLimbs24
        (WindowCaps.balCap 24 17 numLimbs24) (WindowCaps.balCap 24 17 numLimbs24))
      (WindowCaps.limbCap 24 16 numLimbs24) k
      = WindowCaps.wconv (2 * numLimbs24 - 1) numLimbs24
        (fun i => sqBListF.getD i 0) (WindowCaps.limbCap 24 16 numLimbs24) k := by
    apply WindowCaps.wconv_congr
    · intro i
      by_cases hi : i < 2 * numLimbs24 - 1
      · exact sqBcap_eq i hi
      · rw [WindowCaps.wconv_eq_zero_of_ge _ _ (by
          have hn : numLimbs24 = 171 := rfl
          rw [hn] at hi ⊢
          omega),
          List.getD_eq_default _ _ (by
            have hlen : sqBListF.length = 341 := rfl
            have hn : numLimbs24 = 171 := rfl
            rw [hn] at hi
            omega)]
    · intro j; rfl
  rw [hcongr, WindowCaps.wconv_eq_wconvL]
  have h := a2ListF_ok
  rw [List.all_eq_true] at h
  have hk' := h k (List.mem_range.mpr hk)
  exact (beq_iff_eq).mp (by simpa using hk')

/-- Extraction: the `q·n` cap equals `q2ListF`. -/
private lemma q2cap_eq (k : ℕ) (hk : k < 3 * numLimbs24 - 1) :
    WindowCaps.qnCapW 24 16 8 numLimbs24 k = q2ListF.getD k 0 := by
  have h := q2ListF_ok
  rw [List.all_eq_true] at h
  have hk' := h k (List.mem_range.mpr hk)
  exact (beq_iff_eq).mp (by simpa using hk')

/-- LHS adequacy for the balanced fused core: the signed triple-product cap is
`< nfPbalF`. -/
theorem hlhs_adXbal : ∀ k, k < 3 * numLimbs24 - 1 →
    WindowCaps.wconv (2 * numLimbs24 - 1) numLimbs24
      (WindowCaps.wconv numLimbs24 numLimbs24
        (WindowCaps.balCap 24 17 numLimbs24) (WindowCaps.balCap 24 17 numLimbs24))
      (WindowCaps.limbCap 24 16 numLimbs24) k < vparamsXbal.Nf k := by
  intro k hk
  show _ < nfPbalF k
  rw [a2cap_eq k hk]
  unfold nfPbalF
  omega

/-- RHS adequacy for the balanced fused core. -/
theorem hrhs_adXbal : ∀ k, k < 3 * numLimbs24 - 1 →
    WindowCaps.wconv (2 * numLimbs24 - 1) numLimbs24
      (WindowCaps.wconv numLimbs24 numLimbs24
        (WindowCaps.balCap 24 17 numLimbs24) (WindowCaps.balCap 24 17 numLimbs24))
      (WindowCaps.limbCap 24 16 numLimbs24) k
    + WindowCaps.qnCapW 24 16 8 numLimbs24 k
    + (if k < numLimbs24 then WindowCaps.limbCap 24 16 numLimbs24 k else 0) < vparamsXRbal.Nf k := by
  intro k hk
  show _ < nfNbalF k
  rw [a2cap_eq k hk, q2cap_eq k hk]
  unfold nfNbalF
  omega


/-! ## Balanced quad & first squaring battery `GroupedEqD` params (phase 3) -/

def qBListQ : List ℕ := [281474943156225, 562949886312450, 844424829468675, 1125899772624900, 1407374715781125, 1688849658937350, 1970324602093575, 2251799545249800, 2533274488406025, 2814749431562250, 3096224374718475, 3377699317874700, 3659174261030925, 3940649204187150, 4222124147343375, 4503599090499600, 4785074033655825, 5066548976812050, 5348023919968275, 5629498863124500, 5910973806280725, 6192448749436950, 6473923692593175, 6755398635749400, 7036873578905625, 7318348522061850, 7599823465218075, 7881298408374300, 8162773351530525, 8444248294686750, 8725723237842975, 9007198180999200, 9288673124155425, 9570148067311650, 9851623010467875, 10133097953624100, 10414572896780325, 10696047839936550, 10977522783092775, 11258997726249000, 11540472669405225, 11821947612561450, 12103422555717675, 12384897498873900, 12666372442030125, 12947847385186350, 13229322328342575, 13510797271498800, 13792272214655025, 14073747157811250, 14355222100967475, 14636697044123700, 14918171987279925, 15199646930436150, 15481121873592375, 15762596816748600, 16044071759904825, 16325546703061050, 16607021646217275, 16888496589373500, 17169971532529725, 17451446475685950, 17732921418842175, 18014396361998400, 18295871305154625, 18577346248310850, 18858821191467075, 19140296134623300, 19421771077779525, 19703246020935750, 19984720964091975, 20266195907248200, 20547670850404425, 20829145793560650, 21110620736716875, 21392095679873100, 21673570623029325, 21955045566185550, 22236520509341775, 22517995452498000, 22799470395654225, 23080945338810450, 23362420281966675, 23643895225122900, 23925370168279125, 24206845111435350, 24488320054591575, 24769794997747800, 25051269940904025, 25332744884060250, 25614219827216475, 25895694770372700, 26177169713528925, 26458644656685150, 26740119599841375, 27021594542997600, 27303069486153825, 27584544429310050, 27866019372466275, 28147494315622500, 28428969258778725, 28710444201934950, 28991919145091175, 29273394088247400, 29554869031403625, 29836343974559850, 30117818917716075, 30399293860872300, 30680768804028525, 30962243747184750, 31243718690340975, 31525193633497200, 31806668576653425, 32088143519809650, 32369618462965875, 32651093406122100, 32932568349278325, 33214043292434550, 33495518235590775, 33776993178747000, 34058468121903225, 34339943065059450, 34621418008215675, 34902892951371900, 35184367894528125, 35465842837684350, 35747317780840575, 36028792723996800, 36310267667153025, 36591742610309250, 36873217553465475, 37154692496621700, 37436167439777925, 37717642382934150, 37999117326090375, 38280592269246600, 38562067212402825, 38843542155559050, 39125017098715275, 39406492041871500, 39687966985027725, 39969441928183950, 40250916871340175, 40532391814496400, 40813866757652625, 41095341700808850, 41376816643965075, 41658291587121300, 41939766530277525, 42221241473433750, 42502716416589975, 42784191359746200, 43065666302902425, 43347141246058650, 43628616189214875, 43910091132371100, 44191566075527325, 44473041018683550, 44754515961839775, 45035990904996000, 45317465848152225, 45598940791308450, 45880415734464675, 46161890677620900, 46443365620777125, 46724840563933350, 47006315507089575, 47287790450245800, 47569265393402025, 47850740336558250, 47571464382972075, 47289989439815850, 47008514496659625, 46727039553503400, 46445564610347175, 46164089667190950, 45882614724034725, 45601139780878500, 45319664837722275, 45038189894566050, 44756714951409825, 44475240008253600, 44193765065097375, 43912290121941150, 43630815178784925, 43349340235628700, 43067865292472475, 42786390349316250, 42504915406160025, 42223440463003800, 41941965519847575, 41660490576691350, 41379015633535125, 41097540690378900, 40816065747222675, 40534590804066450, 40253115860910225, 39971640917754000, 39690165974597775, 39408691031441550, 39127216088285325, 38845741145129100, 38564266201972875, 38282791258816650, 38001316315660425, 37719841372504200, 37438366429347975, 37156891486191750, 36875416543035525, 36593941599879300, 36312466656723075, 36030991713566850, 35749516770410625, 35468041827254400, 35186566884098175, 34905091940941950, 34623616997785725, 34342142054629500, 34060667111473275, 33779192168317050, 33497717225160825, 33216242282004600, 32934767338848375, 32653292395692150, 32371817452535925, 32090342509379700, 31808867566223475, 31527392623067250, 31245917679911025, 30964442736754800, 30682967793598575, 30401492850442350, 30120017907286125, 29838542964129900, 29557068020973675, 29275593077817450, 28994118134661225, 28712643191505000, 28431168248348775, 28149693305192550, 27868218362036325, 27586743418880100, 27305268475723875, 27023793532567650, 26742318589411425, 26460843646255200, 26179368703098975, 25897893759942750, 25616418816786525, 25334943873630300, 25053468930474075, 24771993987317850, 24490519044161625, 24209044101005400, 23927569157849175, 23646094214692950, 23364619271536725, 23083144328380500, 22801669385224275, 22520194442068050, 22238719498911825, 21957244555755600, 21675769612599375, 21394294669443150, 21112819726286925, 20831344783130700, 20549869839974475, 20268394896818250, 19986919953662025, 19705445010505800, 19423970067349575, 19142495124193350, 18861020181037125, 18579545237880900, 18298070294724675, 18016595351568450, 17735120408412225, 17453645465256000, 17172170522099775, 16890695578943550, 16609220635787325, 16327745692631100, 16046270749474875, 15764795806318650, 15483320863162425, 15201845920006200, 14920370976849975, 14638896033693750, 14357421090537525, 14075946147381300, 13794471204225075, 13512996261068850, 13231521317912625, 12950046374756400, 12668571431600175, 12387096488443950, 12105621545287725, 11824146602131500, 11542671658975275, 11261196715819050, 10979721772662825, 10698246829506600, 10416771886350375, 10135296943194150, 9853822000037925, 9572347056881700, 9290872113725475, 9009397170569250, 8727922227413025, 8446447284256800, 8164972341100575, 7883497397944350, 7602022454788125, 7320547511631900, 7039072568475675, 6757597625319450, 6476122682163225, 6194647739007000, 5913172795850775, 5631697852694550, 5350222909538325, 5068747966382100, 4787273023225875, 4505798080069650, 4224323136913425, 3942848193757200, 3661373250600975, 3379898307444750, 3098423364288525, 2816948421132300, 2535473477976075, 2253998534819850, 1972523591663625, 1691048648507400, 1409573705351175, 1128098762194950, 846623819038725, 565148875882500, 283673932726275, 2198989570050, 4294836225]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem qBListQ_ok : (List.range (2 * numLimbs24 - 1)).all
    (fun k => WindowCaps.wconvL numLimbs24 numLimbs24
      (WindowCaps.limbCap 24 16 numLimbs24) (WindowCaps.limbCap 24 16 numLimbs24) k
        == qBListQ.getD k 0) = true := by decide

/-- Extraction: the balanced square cap equals `sqBListF` (public). -/
theorem sqBcap_eqQ (k : ℕ) (hk : k < 2 * numLimbs24 - 1) :
    WindowCaps.wconv numLimbs24 numLimbs24
      (WindowCaps.balCap 24 17 numLimbs24) (WindowCaps.balCap 24 17 numLimbs24) k
      = sqBListF.getD k 0 := sqBcap_eq k hk

theorem qBcap_eqQ (k : ℕ) (hk : k < 2 * numLimbs24 - 1) :
    WindowCaps.wconv numLimbs24 numLimbs24
      (WindowCaps.limbCap 24 16 numLimbs24) (WindowCaps.limbCap 24 16 numLimbs24) k
      = qBListQ.getD k 0 := by
  have h := qBListQ_ok
  rw [List.all_eq_true] at h
  have hk' := h k (List.mem_range.mpr hk)
  rw [WindowCaps.wconv_eq_wconvL]
  exact (beq_iff_eq).mp (by simpa using hk')

/-- Balanced middle-battery positive/negative flanks. -/
def nfPQbal (j : ℕ) : ℕ :=
  sqBListF.getD j 0 + (if j < numLimbs24 then WindowCaps.balCap 24 17 numLimbs24 j else 0) + 1
def nfNQbal (j : ℕ) : ℕ :=
  sqBListF.getD j 0 + qBListQ.getD j 0
    + (if j < numLimbs24 then WindowCaps.balCap 24 17 numLimbs24 j else 0) + 1

def gfQbal (k : ℕ) : ℕ := if k < 36 then 9 else if k = 36 then 7 else 9
def posOfQbal (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k ≤ 36 then 9 * k else 331 + 9 * (k - 37)

def wtableQbal : List ℕ := [28, 29, 30, 30, 31, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 31, 31, 31, 31, 31, 30, 30, 29, 28]
def offtableQPbal : List ℕ := [37748738, 75497476, 113246215, 150994953, 188743691, 226492429, 264241168, 301989906, 339738644, 377487382, 415236121, 452984859, 490733597, 528482335, 566231074, 603979812, 641728550, 679477288, 708968489, 671219751, 633471013, 595722274, 557973536, 520224798, 482476060, 444727321, 406978583, 369229845, 331481107, 293732368, 255983630, 218234892, 180486154, 142737415, 104988677, 67239939, 37879809]
def offtableQNbal : List ℕ := [188743672, 377487345, 566231019, 754974692, 943718365, 1132462038, 1321205712, 1509949385, 1698693058, 1887436731, 2076180405, 2264924078, 2453667751, 2642411424, 2831155098, 3019898771, 3208642444, 3397386117, 3544448895, 3355705222, 3166961549, 2978217875, 2789474202, 2600730529, 2411986856, 2223243182, 2034499509, 1845755836, 1657012163, 1468268489, 1279524816, 1090781143, 902037470, 713293796, 524550123, 335806450, 189005815]
def wfQbal (k : ℕ) : ℕ := wtableQbal.getD k 19
def offQPbal (k : ℕ) : ℕ := offtableQPbal.getD k 131071
def offQNbal (k : ℕ) : ℕ := offtableQNbal.getD k 262142

def vparamsQbal : GroupedEqV.VParams where
  Nf := nfPQbal
  OFFf := offQPbal
  Wf := wfQbal
  Nmax := 0
  OFFmax := 0
  Wmax := 33
def vparamsQRbal : GroupedEqV.VParams where
  Nf := nfNQbal
  OFFf := offQNbal
  Wf := wfQbal
  Nmax := 0
  OFFmax := 0
  Wmax := 33

private lemma wfQbal_bounds (k : ℕ) : 1 ≤ wfQbal k ∧ wfQbal k ≤ 33 := by
  unfold wfQbal
  by_cases h : k < wtableQbal.length
  · rw [List.getD_eq_getElem _ _ h]
    have hall : ∀ x ∈ wtableQbal, 1 ≤ x ∧ x ≤ 33 := by decide
    exact hall _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨by norm_num, by norm_num⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvxQbal :
    GroupedEqXV.GVXHyps circomPrime (2 * numLimbs24 - 1) 24 gfQbal posOfQbal 39 vparamsQbal vparamsQRbal := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide⟩
  · intro k; simp only [posOfQbal, gfQbal]; split_ifs <;> omega
  · intro k; simp only [gfQbal]; split_ifs <;> omega
  · intro k
    have h := wfQbal_bounds k
    have hWf : vparamsQbal.Wf k = wfQbal k := rfl
    rw [hWf]; refine ⟨by omega, ?_⟩
    calc (2 : ℕ) ^ wfQbal k ≤ 2 ^ 33 := Nat.pow_le_pow_right (by norm_num) h.2
      _ < circomPrime := by decide
  · intro j; exact ⟨by show 1 ≤ nfPQbal j; unfold nfPQbal; omega,
      by show 1 ≤ nfNQbal j; unfold nfNQbal; omega⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvdQbal_window :
    ∀ j, j < 2 * numLimbs24 - 1 → vparamsQbal.Nf j + vparamsQRbal.Nf j ≤ circomPrime := by
  have h : (List.range (2 * numLimbs24 - 1)).all (fun j => nfPQbal j + nfNQbal j ≤ circomPrime) = true := by
    decide
  rw [List.all_eq_true] at h
  intro j hj; have := h j (List.mem_range.mpr hj); simpa using this

theorem hgvdQbal :
    GroupedEqD.GVDHyps circomPrime (2 * numLimbs24 - 1) 24 gfQbal posOfQbal 39 vparamsQbal vparamsQRbal :=
  ⟨hgvxQbal, hgvdQbal_window⟩

theorem hNfDQbal : SquareModBalGT.NfOkD (m := numLimbs24) 24 16 17 vparamsQbal vparamsQRbal := by
  constructor
  · intro j hj
    show WindowCaps.wconv numLimbs24 numLimbs24 (WindowCaps.balCap 24 17 numLimbs24)
        (WindowCaps.balCap 24 17 numLimbs24) j
      + (if j < numLimbs24 then WindowCaps.balCap 24 17 numLimbs24 j else 0) < nfPQbal j
    rw [sqBcap_eqQ j hj]; unfold nfPQbal; omega
  · intro j hj
    show WindowCaps.wconv numLimbs24 numLimbs24 (WindowCaps.balCap 24 17 numLimbs24)
        (WindowCaps.balCap 24 17 numLimbs24) j
      + WindowCaps.wconv numLimbs24 numLimbs24 (WindowCaps.limbCap 24 16 numLimbs24)
        (WindowCaps.limbCap 24 16 numLimbs24) j
      + (if j < numLimbs24 then WindowCaps.balCap 24 17 numLimbs24 j else 0) < nfNQbal j
    rw [sqBcap_eqQ j hj, qBcap_eqQ j hj]; unfold nfNQbal; omega

/-- Balanced first-battery flank (`NfP = NfN`, unsigned lhs square). -/
def nfFbal (j : ℕ) : ℕ :=
  qBListQ.getD j 0 + (if j < numLimbs24 then WindowCaps.balCap 24 17 numLimbs24 j else 0) + 1

def gfFbal (k : ℕ) : ℕ := if k < 2 then 8 else 9
def posOfFbal (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k ≤ 2 then 8 * k else 16 + 9 * (k - 2)

def wtableFbal : List ℕ := [28, 29, 30, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 32, 32, 32, 32, 32, 32, 32, 31, 31, 31, 31, 30, 30, 29]
def offtableFbal : List ℕ := [134217719, 268435439, 419430374, 570425309, 721420244, 872415179, 1023410114, 1174405049, 1325399984, 1476394919, 1627389854, 1778384789, 1929379724, 2080374659, 2231369594, 2382364529, 2533359464, 2684354399, 2835349334, 2718039900, 2567044965, 2416050030, 2265055095, 2114060160, 1963065225, 1812070290, 1661075355, 1510080420, 1359085485, 1208090550, 1057095615, 906100680, 755105745, 604110810, 453115875, 302120940, 151126005]
def wfFbal (k : ℕ) : ℕ := wtableFbal.getD k 18
def offFbal (k : ℕ) : ℕ := offtableFbal.getD k 131070

def vparamsFbal : GroupedEqV.VParams where
  Nf := nfFbal
  OFFf := offFbal
  Wf := wfFbal
  Nmax := 0
  OFFmax := 0
  Wmax := 33

private lemma wfFbal_bounds (k : ℕ) : 1 ≤ wfFbal k ∧ wfFbal k ≤ 33 := by
  unfold wfFbal
  by_cases h : k < wtableFbal.length
  · rw [List.getD_eq_getElem _ _ h]
    have hall : ∀ x ∈ wtableFbal, 1 ≤ x ∧ x ≤ 33 := by decide
    exact hall _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨by norm_num, by norm_num⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvxFbal :
    GroupedEqXV.GVXHyps circomPrime (2 * numLimbs24 - 1) 24 gfFbal posOfFbal 39 vparamsFbal vparamsFbal := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide⟩
  · intro k; simp only [posOfFbal, gfFbal]; split_ifs <;> omega
  · intro k; simp only [gfFbal]; split_ifs <;> omega
  · intro k
    have h := wfFbal_bounds k
    have hWf : vparamsFbal.Wf k = wfFbal k := rfl
    rw [hWf]; refine ⟨by omega, ?_⟩
    calc (2 : ℕ) ^ wfFbal k ≤ 2 ^ 33 := Nat.pow_le_pow_right (by norm_num) h.2
      _ < circomPrime := by decide
  · intro j; exact ⟨by show 1 ≤ nfFbal j; unfold nfFbal; omega,
      by show 1 ≤ nfFbal j; unfold nfFbal; omega⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvdFbal_window :
    ∀ j, j < 2 * numLimbs24 - 1 → vparamsFbal.Nf j + vparamsFbal.Nf j ≤ circomPrime := by
  have h : (List.range (2 * numLimbs24 - 1)).all (fun j => nfFbal j + nfFbal j ≤ circomPrime) = true := by
    decide
  rw [List.all_eq_true] at h
  intro j hj; have := h j (List.mem_range.mpr hj); simpa using this

theorem hgvdFbal :
    GroupedEqD.GVDHyps circomPrime (2 * numLimbs24 - 1) 24 gfFbal posOfFbal 39 vparamsFbal vparamsFbal :=
  ⟨hgvxFbal, hgvdFbal_window⟩

theorem hNfFbal : SquareModBalFirstGT.NfOkF (m := numLimbs24) 24 16 17 vparamsFbal vparamsFbal := by
  constructor <;>
  · intro j hj
    show WindowCaps.wconv numLimbs24 numLimbs24 (WindowCaps.limbCap 24 16 numLimbs24)
        (WindowCaps.limbCap 24 16 numLimbs24) j
      + (if j < numLimbs24 then WindowCaps.balCap 24 17 numLimbs24 j else 0) < nfFbal j
    rw [qBcap_eqQ j hj]; unfold nfFbal; omega

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
