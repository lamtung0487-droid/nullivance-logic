# LOGIC NULLIVANCE (NPL) — BẢN XÂY DỰNG HOÀN CHỈNH
## Triết học nền tảng, đặc tả hình thức, và siêu lý thuyết đã kiểm máy

**Phạm vi:** Tài liệu này là *toàn bộ và chỉ* phần logic của Nullivance.
Không có engine thống kê, không có phân tích dữ liệu, không có ứng dụng.
Mọi định lý đều đã kiểm bằng máy (exhaustive trên lưới [0,1]²) trong phiên này.

**Quy ước trình bày:** mỗi mục hình thức đi kèm một đoạn «Đọc:» — diễn giải
tường minh bằng lời thường. Định nghĩa luôn đứng trước khi dùng.

---

# PHẦN I — NỀN TRIẾT HỌC

## §1. Tiên đề Zero: tách Tồn tại khỏi Hướng

Toàn bộ hệ mọc từ đúng **một** mệnh đề nền:

> **Tiên đề Zero.** Trạng thái của một mệnh đề không quy về một con số.
> Nó gồm hai thành phần độc lập và *khác loại nhau về bản chất*:
> - **α — cường độ tồn tại** ("có bao nhiêu"): tuyệt đối, có nghĩa tự thân,
>   bị chặn trong [0,1] với hai cực đạt được.
> - **Θ — hướng/cấu trúc** ("là loại nào"): tương đối, *chỉ* có nghĩa qua
>   khác biệt với cái khác, không có nghĩa tự thân.

Đọc: mọi logic trước đây gán cho mệnh đề *một* đại lượng tuyệt đối — một bit
(cổ điển), một số trong [0,1] (fuzzy), một cặp bit (FDE). Nullivance là hệ
đầu tiên trong đó đơn vị gốc có **một nửa tuyệt đối và một nửa tương đối**.
Đó không phải trang trí: mọi khác biệt của hệ với các logic khác đều là hệ
quả của sự phân ly này.

## §2. Ba câu hỏi triết học — mỗi câu là một hệ quả của Tiên đề Zero

Ba câu hỏi khởi nguồn của Nullivance, ở dạng đã *sửa lại cho chặt* (dạng cũ
bị phê bình đúng là phát biểu tâm lý/lan man; dạng dưới đây là dạng có nội
dung hình thức).

### Câu hỏi 1 — Nguồn gốc của nghĩa
**Dạng cũ (bỏ):** "tư duy không tự khởi, cần thông tin có trước" — đây là
quan sát tâm lý, không phải định lý, và không cần đúng tuyệt đối.
**Dạng chặt (giữ):** *nghĩa = khác biệt.* Một trạng thái không phân biệt được
với nền của nó thì không mang thông tin. Đây là nội dung chặt (nền của lý
thuyết thông tin), và "tư duy cần cái có trước" chỉ là một ví dụ của nó.
**→ Lựa chọn hình thức:** Θ là đại lượng *tương đối* — Θ của một điểm đơn
độc vô nghĩa; chỉ *hiệu/tương quan* Θ giữa các trạng thái mang nghĩa.

### Câu hỏi 2 — Chân lý thuộc thế giới hay thuộc nhận thức?
**Nội dung:** nếu "logic" có thể là cách bộ não buộc phải nhìn chứ không phải
thuộc tính tuyệt đối của thực tại, thì "đúng/sai" không được phép là primitive.
Nó phải là cái *thô hơn* được lọc từ cái *tinh hơn*.
**→ Lựa chọn hình thức:** chân lý là **phép chiếu ngưỡng** π_τ từ trạng thái
đầy đủ (hai kênh liên tục) xuống bốn trạng thái rồi xuống hai. Logic cổ điển
= cái bóng nhị phân của trạng thái giàu hơn. (Định nghĩa 14–15, §10.)

### Câu hỏi 3 — Cái chưa biểu hiện vẫn tác động (bản thể của hư vô)
**Nội dung:** một thứ "không có mặt" vẫn có thể có *hình* — tiềm năng chưa
bộc lộ. Hư vô không đồng nhất: có hư-vô-rỗng và hư-vô-mang-cấu-trúc.
**→ Lựa chọn hình thức:** vì α và Θ độc lập, trạng thái **α = 0 nhưng Θ khác
trung tính** là hợp lệ: không biểu hiện nhưng có cấu trúc. Đây là
**Quasivance**. Trong ngữ nghĩa logic, nó hiện thân là trạng thái **N**
(Neither), và định lý trung tâm (§12) chứng minh mâu thuẫn có thể bị *đưa về*
trạng thái đó thay vì nổ hoặc treo.

**Mạch xuyên suốt:** cả ba câu hỏi là ba mặt của *một* phân ly — tồn tại
("bao nhiêu") tách khỏi cấu trúc ("loại nào"). Câu 1: nghĩa nằm ở quan hệ
(phía Θ). Câu 2: đúng/sai là phép chiếu của (α,Θ). Câu 3: Θ sống được cả khi
α tắt. Ba câu hỏi không rời nhau — chúng là Tiên đề Zero nhìn từ ba phía.

## §3. Vì sao α ∈ [0,1] — hai cực, không phải vô hạn

α đo **mức độ biểu hiện**, không đo **lượng**. Lượng (bao nhiêu hạt, bao nhiêu
năng lượng) không có trần — nhưng mức độ hiện diện có trần: *hiện diện trọn
vẹn*. Không có "hiện diện hơn cả trọn vẹn", như không có xác suất 1.3.

Ba lý do buộc chặn [0,1]:
1. **Khác loại với lượng.** "Tồn tại vô hạn" trộn mức-độ-biểu-hiện với
   số-lượng — hai phạm trù khác nhau. α thuộc phạm trù thứ nhất, có cực đại.
2. **Giữ các mốc tuyệt đối.** Độ khớp giữa hai trạng thái tỉ lệ với tích các α
   và phần tương quan Θ; chặn α giữ toàn bộ thang khớp trong một đoạn có hai
   cực tuyệt đối (hoàn toàn tương thích / hoàn toàn đối nghịch). Không có mốc
   tuyệt đối thì không phân loại được trạng thái (T/F/B/N) — hệ sụp thành
   thang trượt không đáy.
3. **Cực 0 phải đạt được.** Quasivance sống *tại đúng điểm* α = 0 — cần một
   chân trời vắng-mặt có thật, không phải tiệm cận. [0,1] đóng cho hai chân
   trời thật; [0,∞) lấy mất trần và biến đáy thành chỉ-tiệm-cận.

## §4. Vì sao Θ không quy về α — "cùng lượng, khác loại"

Phản biện mạnh nhất: *"có α là có khác biệt rồi, cần gì Θ?"* Trả lời:

**α phân biệt được "bao nhiêu", nhưng mù trước "loại nào".** Hai trạng thái
cùng α = 0.5: một cái là 0.5 *vì giằng co dữ dội giữa khẳng định và phủ định*,
cái kia là 0.5 *vì trung tính thật, không nghiêng đâu*. Cùng lượng — khác hẳn
bản chất. Khác biệt đó không nằm trên trục nhiều/ít; nó là khác biệt về
*cấu trúc*, và chỉ Θ bắt được.

Hệ quả quan trọng nhất nằm ở α = 0: nếu chỉ có α, *mọi* cái không-tồn-tại
đồng nhất (đều bằng 0, hết chuyện) — hư vô là một. Có Θ, hư vô có *nhiều
loại*: rỗng thật (Θ trung tính) và mang hình chưa bật sáng (Θ lệch). Bỏ Θ là
mất Quasivance — mất toàn bộ cái mới của hệ.

Gọn: **α đo có bao nhiêu; Θ đo là loại nào. Khác-loại-cùng-lượng là cái α mù
còn Θ thấy.**

## §5. Vì sao đây không phải lý thuyết thông tin đội tên

Phải sòng phẳng: phần "nghĩa = khác biệt" *trùng* Shannon. Nếu hệ dừng ở đo
độ-khác-của-cường-độ thì phê bình "chỉ là thống kê" đúng. Hệ khác Shannon ở
đúng ba điểm, đều do Θ:

1. **Khác biệt có dấu/hướng.** Shannon đo *bao nhiêu* bất định; nó không có
   khái niệm hai trạng thái "cùng hướng", "ngược hướng", hay "trực giao".
   Trong Shannon, mâu thuẫn và độc-lập đều chỉ là "khác X bit". Θ tách chúng.
2. **Phân biệt trạng thái cùng-entropy.** Hai phân bố cùng entropy có thể khác
   Θ ("giằng co" vs "rỗng" ở §4). Entropy mù trước khác biệt này.
3. **Cấu trúc tại xác suất 0.** Shannon định nghĩa thông tin *trên* các sự
   kiện có xác suất dương; sự kiện xác suất 0 vô hình với nó (đóng góp
   entropy = 0 theo định nghĩa). Quasivance — cấu trúc tại α = 0 — là thứ
   Shannon *về mặt định nghĩa* không biểu đạt được. Đây là điểm phân biệt
   cứng nhất, khó bác nhất.

## §6. Chân lý chạy trên nền này thế nào

Cơ chế: **chân lý là cái bóng của nền, chiếu qua ngưỡng.**

- Ở vùng mọi mệnh đề biểu hiện *sạch* (α cao, hướng dứt khoát), phép chiếu
  cho đúng logic cổ điển — mọi suy diễn quen thuộc chạy **nguyên vẹn**.
  (Đây không phải khẩu hiệu: Định lý 7 (§14) chứng minh NPL là mở rộng bảo
  toàn của FDE trên {¬,∧,∨}; hạn chế tiếp xuống {T,F} là logic cổ điển.)
- Chân lý cổ điển chỉ *vỡ* ở hai mép: vùng **B** (mâu thuẫn — cổ điển nổ,
  explosion) và vùng **N** (chưa biểu hiện — cổ điển không có khái niệm).
  Đúng tại hai mép đó, nền tiếp quản: giữ B như trạng thái hợp lệ, và có
  toán tử ⊕ đưa mâu thuẫn về N (§12).

Loại suy (chỉ là loại suy, không phải chứng minh): logic cổ điển đối với NPL
như cơ học cổ điển đối với lý thuyết nền — trùng khít ở vùng "năng lượng
thấp", vỡ ở mép (lõi xoáy / mâu thuẫn), và tại mép thì tầng dưới tiếp quản.

---

# PHẦN II — KIẾN TRÚC BA TẦNG

Hệ được tổ chức thành ba tầng, tách bạch để rõ cái gì là *bản chất* và cái
gì là *lựa chọn có thể thay*:

```
TẦNG 1 — SINH (generative):  (α_T, Θ_T) và (α_F, Θ_F) cho mỗi mệnh đề nguyên tử
        │  qua hàm ổn định Φ
        ▼
TẦNG 2 — NGỮ NGHĨA (semantic engine):  vật chân lý (t, f) ∈ [0,1]²
        │  qua phép chiếu ngưỡng π_τ
        ▼
TẦNG 3 — CHIẾU (projection):  bốn trạng thái T / F / B / N  →  (ép tiếp) {Đúng, Sai}
```

**Điểm nghiêm ngặt quan trọng:** mọi siêu định lý của logic (§14) chỉ phụ
thuộc Tầng 2 — tức cặp (t,f) và bảng phép nối. Chúng **không phụ thuộc dạng
cụ thể của Φ** hay cách Tầng 1 sinh ra (t,f). Tầng 1 là *câu chuyện nguồn
gốc* (và là nơi triết học α–Θ sống); có thể thay Φ khác mà logic không đổi.
Tách như vậy để: (a) phản biện vào dạng Φ không chạm được vào logic;
(b) rõ ràng đâu là đóng góp logic, đâu là mô hình sinh.

## §7. Tầng 1 — tầng sinh

**Định nghĩa 1 (kênh hỗ trợ).** Mỗi mệnh đề nguyên tử p có **hai kênh độc
lập**: kênh hỗ-trợ-đúng mang (α_T(p), Θ_T(p)) và kênh hỗ-trợ-sai mang
(α_F(p), Θ_F(p)), với α ∈ [0,1], Θ ∈ [0,1]^d.

Đọc: đây là chỗ paraconsistency bắt đầu. Hệ không giữ *một* đại lượng "độ
đúng" rồi lấy phần bù làm "độ sai" — nó giữ **bằng chứng cho** và **bằng
chứng chống** như hai thực thể riêng, có thể *cùng mạnh* (mâu thuẫn thật)
hoặc *cùng yếu* (chưa biểu hiện). Fuzzy chỉ có một kênh nên không làm được
cả hai điều đó.

**Định nghĩa 2 (tọa độ phân cực Θ và hàm ổn định).** Trong *logic* này,
Θ_k ∈ [0,1] là **tọa độ phân cực**: 0.5 là điểm trung hòa; 0 và 1 là hai cực
phân cực; phép lật x ↦ 1−x là "quay 180°". Hàm ổn định từng thành phần:
f(x) = 1 − 2|x − 0.5| (cực đại 1 tại trung hòa, bằng 0 tại hai cực), và độ
ổn định toàn cục là trung bình nhân Φ(Θ) = (∏_k f(Θ_k))^{1/d} (dạng log để
ổn định số). Bổ đề bất biến: Φ(1−Θ) = Φ(Θ).

Đọc — và một minh định trung thực: Θ ở đây **không phải** pha vật lý trên
vòng tròn (như trong các thảo luận vật lý của Nullivance). Nó là một tọa độ
phân cực bị chặn, trong đó phép lật quanh 0.5 đóng vai "đảo pha 180°". Hai
cấu trúc có họ hàng (lật ↔ quay nửa vòng) nhưng không đồng nhất; tài liệu
này dùng nhất quán nghĩa tọa-độ-phân-cực.

**Định nghĩa 3 (sinh vật chân lý).**
t(p) := α_T(p)·Φ(Θ_T(p)),  f(p) := α_F(p)·Φ(Θ_F(p)).

Đọc: mỗi kênh đóng góp một *cường độ hiệu dụng* = cường độ tồn tại × độ ổn
định cấu trúc. Kể từ đây, logic chỉ cần cặp (t,f); Tầng 1 đã xong vai trò.

**Định nghĩa 4 (Quasivance, tại tầng sinh).** Trạng thái có α ≈ 0 nhưng
Θ khác trung tính: không biểu hiện (mọi cường độ hiệu dụng ≈ 0) nhưng mang
cấu trúc. Hình thức hóa đầy đủ ở Tầng 2–3: trạng thái N (§10) — và Định lý
trung tâm (§12) cho thấy N có thể được *sinh ra* từ mâu thuẫn, không chỉ
được *gán sẵn*.

---

# PHẦN III — CÚ PHÁP

**Định nghĩa 5 (bảng chữ).** Vô hạn đếm được các mệnh đề nguyên tử p, q, r,…;
các phép nối nguyên thủy ¬, ∧, ∨, ⊕; dấu ngoặc.

**Định nghĩa 6 (công thức, văn phạm BNF).**
φ ::= p | ¬φ | (φ ∧ ψ) | (φ ∨ ψ) | (φ ⊕ ψ)
Viết tắt: φ ⇒ ψ := ¬φ ∨ ψ (chỉ là ký hiệu tắt, không phải phép nối nguyên thủy).

**Định nghĩa 7 (độ ưu tiên).** ¬ > ∧ > ∨ > ⊕ > ⇒.

---

# PHẦN IV — NGỮ NGHĨA (TẦNG 2)

## §8. Mô hình và vật chân lý

**Định nghĩa 8 (mô hình).** Một mô hình NPL là bộ M = (v, τ) trong đó v gán
cho mỗi nguyên tử p một **vật chân lý** V(p) = (t(p), f(p)) ∈ [0,1]², và
τ ∈ (0,1] là **ngưỡng biểu hiện**.

Đọc: t = mức hỗ trợ cho tính đúng, f = mức hỗ trợ cho tính sai, độc lập nhau.
τ là "mức đủ để tính là biểu hiện" — tham số của phép chiếu chân lý (Câu hỏi 2).

## §9. Bảng phép nối — giải thích từng phép

**Định nghĩa 9 (định giá hợp thức).** V mở rộng lên mọi công thức:

| φ | t(φ) | f(φ) |
|---|---|---|
| ¬ψ | f(ψ) | t(ψ) |
| ψ ∧ χ | min(t(ψ), t(χ)) | max(f(ψ), f(χ)) |
| ψ ∨ χ | max(t(ψ), t(χ)) | min(f(ψ), f(χ)) |
| ψ ⊕ χ | min(t(ψ), t(χ)) | min(f(ψ), f(χ)) |

Đọc từng dòng:

**¬ là HOÁN ĐỔI, không phải "1 trừ".** Phủ định không phá hủy hay đảo nội
dung — nó *đổi vai* hai kênh: bằng-chứng-cho thành bằng-chứng-chống và ngược
lại. Hệ quả tức thì: ¬¬φ = φ (hoán đổi hai lần về chỗ cũ), và phủ định *bảo
toàn thông tin* — một mâu thuẫn (t,f cùng cao) vẫn là mâu thuẫn sau phủ định.
Đây là phủ định chuẩn của họ FDE/bilattice, và là lựa chọn *bắt buộc* nếu
muốn De Morgan đúng (đã kiểm máy: ¬(A∧B)=¬A∨¬B, ¬(A∨B)=¬A∧¬B đều PASS).

**∧ thận trọng với đúng, tích lũy cái sai.** t lấy min: hội chỉ đúng tới mức
mắt xích yếu nhất. f lấy max: *mọi* bằng chứng chống một vế đều là bằng chứng
chống cả hội. Bi quan có chủ đích — đúng tinh thần "hội".

**∨ đối ngẫu với ∧** (qua De Morgan): lạc quan với đúng (max), dè dặt với
sai (min).

**⊕ — hòa hợp: chỉ giữ phần CHUNG trên cả hai kênh.** Nhận xét cấu trúc gọn
(đã kiểm máy): ⊕ lấy *luật-t của ∧* và *luật-f của ∨*. Nghĩa là: khắt khe
như hội về tính đúng, khoan dung như tuyển về tính sai — chỉ những gì *cả
hai bên cùng công nhận* (cả phần tin lẫn phần chống) mới đi qua. Đây là phép
nối "đồng thuận".

## §10. Biểu hiện, bốn trạng thái, và phép chiếu chân lý

**Định nghĩa 10 (thỏa mãn).** M ⊨ φ  ⇔  t(φ) ≥ τ.

**Định nghĩa 11 (bốn trạng thái cảm sinh bởi τ).**
- **T** (đúng biểu hiện):   t ≥ τ, f < τ
- **F** (sai biểu hiện):    t < τ, f ≥ τ
- **B** (mâu thuẫn biểu hiện — Both):  t ≥ τ, f ≥ τ
- **N** (chưa biểu hiện — Neither):    t < τ, f < τ
Tập chỉ định (designated): {T, B}.

**Định nghĩa 12 (hệ quả logic).** Γ ⊨ φ ⇔ mọi mô hình thỏa toàn bộ Γ đều thỏa φ.

**Định nghĩa 13 (phép chiếu chân lý cổ điển).** Ép FOUR xuống {T, F} bằng
cách loại B và N. Logic cổ điển là kết quả của *hai* lần chiếu:
(t,f) --π_τ--> {T,F,B,N} --loại B,N--> {Đúng, Sai}.

Đọc: đây là nội dung hình thức của Câu hỏi 2. Mỗi lần chiếu *vứt* thông tin:
lần một vứt độ lớn liên tục (giữ so-với-ngưỡng), lần hai vứt hẳn hai trạng
thái mép. Chân lý cổ điển là cái còn lại sau hai lần vứt — và hai trạng thái
bị vứt (B, N) chính là hai chỗ nó vỡ khi gặp thực tế (mâu thuẫn, tiềm ẩn).

## §11. Hai trật tự — cấu trúc bilattice, và ĐỊNH VỊ TRUNG THỰC

**Định nghĩa 14 (hai trật tự trên [0,1]²).**
- Trật tự **chân lý** ≤_t:  (t₁,f₁) ≤_t (t₂,f₂) ⇔ t₁ ≤ t₂ và f₁ ≥ f₂
  ("đúng hơn" = nhiều hỗ trợ đúng hơn và ít hỗ trợ sai hơn).
- Trật tự **tri thức** ≤_k: (t₁,f₁) ≤_k (t₂,f₂) ⇔ t₁ ≤ t₂ và f₁ ≤ f₂
  ("biết nhiều hơn" = nhiều bằng chứng hơn ở cả hai phía, kể cả xung đột).

**Mệnh đề 1 (đã kiểm máy).** ∧ và ∨ là meet/join theo ≤_t. **⊕ là meet theo
≤_k.** Trên bốn đỉnh {T,F,B,N}, thứ tự tri thức có N ở đáy, B ở đỉnh, và:
T⊕F = N; B⊕x = x; N⊕x = N (bảng đã kiểm).

**ĐỊNH VỊ TRUNG THỰC — bắt buộc ghi rõ:** cấu trúc hai-trật-tự này là
**bilattice**, đã có trong văn hiến: Ginsberg (1988), Fitting (1991), và đặc
biệt Arieli & Avron (1996) đã nghiên cứu logic trên bilattice với các toán
tử tri thức trong ngôn ngữ. Phép ⊕ của NPL, khi hạn chế xuống FOUR, **trùng
với toán tử consensus** (thường ký hiệu ⊗) của văn hiến bilattice. *(Lưu ý
va chạm ký hiệu: văn hiến dùng ⊕ cho knowledge-JOIN (max,max) — "cả tin";
NPL dùng ⊕ cho knowledge-MEET — "đồng thuận". Bài nộp phải ghi chú va chạm
này.)* Do đó **không được** tuyên bố "chưa logic nào có toán tử này" — phiên
bản rời rạc đã tồn tại. Đóng góp thật của NPL hẹp hơn và được liệt kê chính
xác ở §16.

---

# PHẦN V — ĐỊNH LÝ TRUNG TÂM VÀ ĐẠI SỐ CỦA ⊕

## §12. Định lý sập-tiềm-ẩn (latent collapse)

**Định lý 1 (sập-tiềm-ẩn của mâu thuẫn).** Với mọi φ có V(φ) = (t,f):
V(φ ⊕ ¬φ) = (m, m) với m = min(t, f).
Hệ quả: nếu τ > m thì φ⊕¬φ có trạng thái **N**. Đặc biệt, với φ "sạch"
(t·f = 0, không glut), φ⊕¬φ là N với *mọi* τ ∈ (0,1].

*Chứng minh.* V(¬φ) = (f,t). t(φ⊕¬φ) = min(t,f) = m; f(φ⊕¬φ) = min(f,t) = m. ∎
*(Kiểm máy: exhaustive trên lưới, PASS.)*

**So sánh ba hệ trước cùng một mâu thuẫn (φ, ¬φ):**
- Logic cổ điển: **nổ** — từ mâu thuẫn suy ra mọi thứ, hệ chết.
- FDE: chịu được, nhưng giữ mâu thuẫn ở **B** — *biểu hiện* vĩnh viễn.
- NPL với ⊕: đưa mâu thuẫn về **N** — *tiềm ẩn hóa*.

Đọc — và đây là chỗ triết học với toán khớp nhau chặt nhất: ⊕ là **cơ chế
hình thức biến một mâu thuẫn đang biểu hiện thành một trạng thái tiềm ẩn**.
Không khẳng định, không phủ định, không nổ, không treo ở "vừa-đúng-vừa-sai" —
mà *rút về chưa-biểu-hiện*, đúng nghĩa Quasivance của Câu hỏi 3: xung đột
không bị xóa, nó được đưa xuống dạng tiềm năng. N ở đây không phải "không
biết gì" thụ động; nó là *tàn dư có cấu trúc* của một xung đột — và ở Tầng 1,
đó chính là trạng thái α ≈ 0, Θ ≠ trung tính.

## §13. Đại số của ⊕ (đã kiểm máy toàn bộ)

**Mệnh đề 2.** ⊕ giao hoán, kết hợp, lũy đẳng (φ⊕φ ≡ φ), có đơn vị là
B = (1,1), và **tự đối ngẫu qua phủ định**: ¬(φ⊕ψ) ≡ ¬φ ⊕ ¬ψ.
Vậy (công thức/≡, ⊕) là một nửa-dàn giao hoán có đơn vị.

Đọc từng tính chất: lũy đẳng — đồng thuận với chính mình là chính mình; đơn
vị B — hòa hợp với "chấp nhận tất" không đổi gì (B là đỉnh tri thức, meet với
đỉnh là chính mình); tự đối ngẫu — phủ định *xuyên qua* phép hòa hợp mà không
đổi dạng, khác hẳn ∧/∨ (phủ định lật ∧ thành ∨). Hòa hợp là phép nối "trung
lập với phủ định" — đúng tính chất một phép *đồng thuận* nên có.

---

# PHẦN VI — LÝ THUYẾT CHỨNG MINH

## §14. Hệ suy diễn tự nhiên

**Phủ định:** ¬¬φ ⊣⊢ φ. De Morgan: ¬(φ∧ψ) ⊣⊢ ¬φ∨¬ψ; ¬(φ∨ψ) ⊣⊢ ¬φ∧¬ψ.
**Hội:** φ, ψ ⊢ φ∧ψ;  φ∧ψ ⊢ φ;  φ∧ψ ⊢ ψ.
**Tuyển:** φ ⊢ φ∨ψ;  ψ ⊢ φ∨ψ;  (∨-Elim) từ φ∨ψ, [φ]⊢χ, [ψ]⊢χ suy ra χ.
**Hòa hợp:**
- (⊕-Intro) φ, ψ ⊢ φ⊕ψ.
- (⊕-Elim) φ⊕ψ ⊢ φ  và  φ⊕ψ ⊢ ψ.  **[MỚI — sound, đã kiểm máy]**
- (⊕-DeMorgan) ¬(φ⊕ψ) ⊣⊢ ¬φ⊕¬ψ (từ tính tự đối ngẫu, Mệnh đề 2).

**Chứng minh tính sound của ⊕-Elim.** M ⊨ φ⊕ψ nghĩa là min(t(φ),t(ψ)) ≥ τ,
suy ra *cả* t(φ) ≥ τ *và* t(ψ) ≥ τ, tức M ⊨ φ và M ⊨ ψ. ∎
*(Kiểm máy exhaustive mọi cặp lưới, mọi τ: PASS.)*

Đọc: bản nộp trước *hoãn* ⊕-Elim vì e ngại kênh f. Kiểm lại cho thấy nỗi e
ngại đặt sai chỗ: quan hệ thỏa mãn chỉ đọc kênh t, và trên kênh t thì min
cho phép khử an toàn. Món nợ "⊕ chỉ có nửa luật" **đã trả được một nửa**:
Intro và Elim đều có, đều sound. Nửa còn lại (completeness) vẫn nợ — §17.

**Các luật CẤM (bản chất paraconsistent):** ex falso (⊥ ⊢ ψ), explosion
(φ, ¬φ ⊢ ψ), tam đoạn tuyển (φ∨ψ, ¬φ ⊢ ψ) — đều loại.

**Cảnh báo cấu trúc quan trọng (đã kiểm máy):** φ∧ψ và φ⊕ψ *suy diễn được
lẫn nhau* (cùng kênh t) nhưng **tách nhau dưới phủ định**: tồn tại mô hình
mà ¬(φ∧ψ) được chỉ định còn ¬(φ⊕ψ) thì không (nhân chứng: φ=B, ψ=T cho
t(¬(φ∧ψ))=1 nhưng t(¬(φ⊕ψ))=0). Hệ quả: **hệ không được phép có luật
thay-thế-tương-đương không hạn chế** — thay φ∧ψ bằng φ⊕ψ bên trong ngữ cảnh
¬ là KHÔNG sound. Hệ là *phi-đồng-dư* (non-congruential) đối với suy diễn
tương hỗ; tương đương chỉ được thay thế khi là tương đương *giá trị* (≡ trên
(t,f)), không phải tương đương *suy diễn* (⊣⊢). Bài nộp phải ghi rõ điểm này
— nó là loại chi tiết mà reviewer logic dùng để thử độ chín của một hệ.

---

# PHẦN VII — SIÊU LÝ THUYẾT (TẤT CẢ ĐÃ KIỂM MÁY)

## §15. Các định lý

**Định lý 2 (Chặn).** Với mọi φ, M: V(φ) ∈ [0,1]².
*Chứng minh:* quy nạp cấu trúc; min, max, hoán đổi bảo toàn [0,1]². ∎

**Định lý 3 (Không nổ — paraconsistency cấu trúc).** {φ, ¬φ} ⊭ ψ.
*Chứng minh (nhân chứng):* V(p) = (1,1) → V(¬p) = (1,1); V(q) = (0,0).
Mọi τ ∈ (0,1]: M ⊨ p, M ⊨ ¬p, M ⊭ q. Không phụ thuộc chọn τ. ∎

Đọc: mâu thuẫn *mạnh nhất có thể* (p vừa hoàn toàn được hỗ trợ đúng vừa hoàn
toàn được hỗ trợ sai) vẫn không kéo được một mệnh đề trắng (q ở N) thành
được chỉ định. Không nổ là *cấu trúc* của ngữ nghĩa hai kênh, không phải
tình cờ của tham số.

**Định lý 4 (Sound).** Nếu Γ ⊢ φ thì Γ ⊨ φ.
*Chứng minh:* từng luật bảo toàn tính được-chỉ-định; các luật ⊕ đã chứng ở
§14; các luật FDE là chuẩn. ∎

**Định lý 5 (Bảo toàn trên FDE).** Trên mảnh {¬,∧,∨}, quan hệ hệ quả cảm
sinh bởi τ trùng với FDE: phép chiếu π_τ đưa [0,1]² về FOUR và các bảng phép
nối (Định nghĩa 9) rút về đúng bảng Belnap (kiểm máy: ¬, ∧, ∨ khớp toàn bộ
4×4). Completeness của Belnap chuyển giao cho mảnh này. ∎

Đọc: đây là nội dung chặt của "chân lý chạy nguyên trên nền" (§6). NPL không
sửa một dấu phẩy nào của suy diễn quen thuộc ở vùng sạch — nó chỉ *thêm* ⊕
và *giữ* thông tin ở hai mép B, N.

## §16. Bảng trạng thái kiểm máy

| Mệnh đề | Phương pháp | Trạng thái |
|---|---|---|
| Bảng ¬,∧,∨ khớp Belnap trên FOUR (cả ∧ lẫn ∨) | 4×4 toàn bộ | ✓ |
| ⊕ trên FOUR = knowledge-meet (consensus) | bảng 4×4 | ✓ |
| Định lý 1: V(φ⊕¬φ) = (m,m) | lưới toàn bộ | ✓ |
| Mệnh đề 2: giao hoán/kết hợp/lũy đẳng/đơn vị B/tự đối ngẫu | lưới | ✓ |
| Định lý 2: chặn | lưới, mọi phép | ✓ |
| Định lý 3: không nổ | nhân chứng, mọi τ | ✓ |
| ⊕-Elim sound | lưới toàn bộ × mọi τ | ✓ |
| Phi-đồng-dư (∧/⊕ tách dưới ¬) | nhân chứng B,T | ✓ |
| ∧,∨ = meet/join theo ≤_t; ⊕ = meet theo ≤_k | lưới | ✓ |
| ¬¬φ=φ; De Morgan ∧/∨ | lưới | ✓ |

---

# PHẦN VIII — ĐÓNG GÓP THẬT, NỢ MỞ, VÀ NHỮNG GÌ KHÔNG TUYÊN BỐ

## §17. Đóng góp thật (sau khi định vị trung thực với văn hiến)

Vì phần đại số trùng bilattice (§11), tuyên bố đóng góp phải thu hẹp về đúng
những gì mới:

1. **Tầng sinh (α, Θ) và triết học của nó** — sự phân ly tồn-tại/hướng (Tiên
   đề Zero), lập luận [0,1] hai cực, tính không-quy-về-α của Θ, và phân biệt
   với Shannon (đặc biệt: cấu trúc tại α=0). Đây là phần *của riêng*
   Nullivance — văn hiến bilattice không có tầng sinh này và không có cách
   đọc "tiềm ẩn/Quasivance".
2. **Định lý sập-tiềm-ẩn như kết quả trung tâm được đặt tên** — cách đọc
   "consensus đưa mâu thuẫn về latent" gắn với Quasivance là đóng góp diễn
   giải + việc phát biểu nó thành định lý tường minh (m,m) trên ngữ nghĩa
   liên tục có ngưỡng.
3. **Trình bày có ngưỡng τ trên [0,1]² với siêu lý thuyết kiểm máy** — gói
   bảo-toàn-FDE + không-nổ + sound + ⊕-Elim thành một hệ được xác minh
   exhaustive, kèm cảnh báo phi-đồng-dư.

## §18. Nợ mở (ghi thẳng trong bài nộp)

1. **Completeness cho ngôn ngữ đầy đủ có ⊕.** Đã có Intro + Elim + tự đối
   ngẫu (đều sound); *chưa có* chứng minh rằng bộ luật này là *đủ* (mọi hệ
   quả ngữ nghĩa đều suy diễn được). Đây là món nợ hình thức lớn nhất còn lại.
   Điểm tựa: so sánh/nhúng vào hệ của Arieli–Avron (1996) là con đường khả dĩ.
2. **Strong completeness trên ngữ nghĩa liên tục** (ngoài mảnh FDE).
3. **Knowledge-join (max,max).** Bilattice có phép đối ngẫu của ⊕ ("cả tin" —
   gộp mọi bằng chứng, đẩy về B). NPL hiện *chọn không* đưa vào ngôn ngữ;
   phải ghi rõ đây là lựa chọn thiết kế (hệ chỉ quan tâm chiều tiềm-ẩn-hóa)
   hoặc bổ sung ở phần sau.

## §19. Những gì NPL KHÔNG tuyên bố

- KHÔNG tuyên bố là công cụ phân tích dữ liệu (phần đó là bài khác, với
  đối thủ khác — thống kê/ML; xem ranh giới logic ≠ biểu diễn).
- KHÔNG tuyên bố phát minh phép consensus (đã có trong bilattice — §11).
- KHÔNG tuyên bố ứng dụng vật lý, nhận thức, sinh học trong bài logic này.
- KHÔNG tuyên bố tính "sâu sắc" của triết học; triết học ở đây chỉ làm đúng
  một việc: mỗi câu hỏi dẫn ra đúng một lựa chọn hình thức, kiểm được.

## §20. Tài liệu phải trích (đúng chỗ, trong thân bài)

- Belnap (1977), Dunn (1976) — FDE, bốn giá trị. [Định lý 5, §10]
- Ginsberg (1988) — bilattice. [§11]
- Fitting (1991) — bilattice trong ngữ nghĩa logic. [§11]
- Arieli & Avron (1996) — logic của bilattice logic, quan hệ hệ quả, các
  toán tử tri thức trong ngôn ngữ. [§11, §18 — đối chiếu gần nhất]
- Priest (1979) — LP, dialetheism. [so sánh xử lý mâu thuẫn]
- Shannon (1948) — đối chiếu ở §5.

---

*Hết. Mọi mệnh đề hình thức trong tài liệu này hoặc có chứng minh kèm theo,
hoặc có dòng tương ứng trong bảng kiểm máy §16, hoặc được ghi rõ là NỢ (§18).*
