---
title: "Nullivance Logic v2.0"
subtitle: "Bản chứng minh chi tiết cho four-signed analytic calculus, FOUR matrix completeness, và continuous lift"
author: "Bản thảo nghiên cứu tiếp theo"
date: "31 tháng 3 năm 2026"
lang: vi-VN
toc: true
toc-depth: 3
numbersections: true
geometry: margin=1in
fontsize: 11pt
---

# Tóm tắt

Tài liệu này tiếp tục chương trình hoàn chỉnh hóa **Nullivance Logic v2.0** bằng cách viết ra bản chứng minh chi tiết cho phần meta-theory còn dang dở: (i) exact threshold projection từ semantics liên tục $[0,1]^2$ xuống FOUR; (ii) soundness của four-signed analytic calculus; (iii) existence theorem cho open saturated branch; (iv) completeness của calculus trên FOUR matrix; và (v) lifting theorem từ FOUR trở lại continuous NPL.

Tinh thần xuyên suốt là: **không thay thế Nullivance gốc**. State layer $(\sigma,\alpha,\Theta,\rho,\delta)$, truth-object $(t,f)$, và ngữ nghĩa của các connective $\neg,\land,\lor,\oplus$ đều được giữ nguyên. Bước nghiên cứu ở đây chỉ làm một việc: dựng cỗ máy chứng minh đủ chặt để formal core của Nullivance có thể được xem như một hệ logic đóng.

# 1. Mục tiêu và phạm vi

Trong tài liệu này, tôi chỉ chứng minh phần formal core. Điều đó có nghĩa là:

- tôi làm việc với **truth-object** $V(\varphi)=(t(\varphi),f(\varphi))\in[0,1]^2$;
- tôi giữ nguyên các clause của NPL-2D cho $\neg,\land,\lor,\oplus$;
- tôi phát triển proof theory dưới dạng **four-signed analytic calculus**;
- tôi chứng minh completeness trước trên **FOUR matrix**, rồi nâng trở lại semantics liên tục bằng projection theorem.

Phần operational của Nullivance như A7, A7b, A8, pattern field, quasivance field không bị loại bỏ; nhưng chúng không tham gia trực tiếp vào chứng minh completeness của entailment. Chúng là lớp quan sát và động lực học của hệ, không phải luật suy diễn lõi.

# 2. Ngôn ngữ, ngữ nghĩa và bốn meta-signs

## 2.1. Cú pháp

Ngôn ngữ mệnh đề của NPL v2.0 là:

$$
\varphi ::= p \mid \neg\varphi \mid (\varphi\land\psi) \mid (\varphi\lor\psi) \mid (\varphi\oplus\psi).
$$

## 2.2. Semantics liên tục

Trong một mô hình $M=(d,v,\tau)$, mỗi công thức nhận một truth-object

$$
V_M(\varphi)=(t_M(\varphi),f_M(\varphi))\in[0,1]^2.
$$

Các connective được hiểu như sau:

$$
V_M(\neg\varphi)=(f_M(\varphi),t_M(\varphi)),
$$

$$
V_M(\varphi\land\psi)=\big(\min(t_M(\varphi),t_M(\psi)),\max(f_M(\varphi),f_M(\psi))\big),
$$

$$
V_M(\varphi\lor\psi)=\big(\max(t_M(\varphi),t_M(\psi)),\min(f_M(\varphi),f_M(\psi))\big),
$$

$$
V_M(\varphi\oplus\psi)=\big(\min(t_M(\varphi),t_M(\psi)),\min(f_M(\varphi),f_M(\psi))\big).
$$

## 2.3. Bốn meta-signs

Với ngưỡng $\tau\in(0,1]$, ta định nghĩa:

$$
M\models T^+\varphi \iff t_M(\varphi)\ge \tau,
$$

$$
M\models T^-\varphi \iff t_M(\varphi)< \tau,
$$

$$
M\models F^+\varphi \iff f_M(\varphi)\ge \tau,
$$

$$
M\models F^-\varphi \iff f_M(\varphi)< \tau.
$$

Unsigned reading cũ được giữ như projection:

$$
M\models_{old}\varphi \iff M\models T^+\varphi.
$$

## 2.4. Phép đối sign

Để dựng tableau cho entailment, ta dùng phép đối sign:

$$
\overline{T^+}=T^-,\qquad \overline{T^-}=T^+,
$$

$$
\overline{F^+}=F^-,\qquad \overline{F^-}=F^+.
$$

Với một signed formula $S\varphi$, ký hiệu $\overline{S\varphi}$ nghĩa là $\bar S\varphi$.

# 3. FOUR matrix và exact projection

## 3.1. Ma trận FOUR

Sau ngưỡng hóa, mỗi công thức chỉ còn một trong bốn trạng thái:

$$
T=(1,0),\quad F=(0,1),\quad B=(1,1),\quad N=(0,0).
$$

Bit thứ nhất là projected truth-channel; bit thứ hai là projected falsity-channel.

Ta định nghĩa các connective trên FOUR bằng cùng công thức tọa độ:

$$
\neg(x,y)=(y,x),
$$

$$
(x_1,y_1)\land(x_2,y_2)=(\min(x_1,x_2),\max(y_1,y_2)),
$$

$$
(x_1,y_1)\lor(x_2,y_2)=(\max(x_1,x_2),\min(y_1,y_2)),
$$

$$
(x_1,y_1)\oplus(x_2,y_2)=(\min(x_1,x_2),\min(y_1,y_2)).
$$

## 3.2. Phép chiếu ngưỡng

Đặt

$$
\pi_\tau(x,y)=\big(\mathbf 1[x\ge \tau],\mathbf 1[y\ge \tau]\big)\in FOUR.
$$

Với một mô hình liên tục $M$, ta định nghĩa projected valuation trên atom:

$$
v_M^\pi(p)=\pi_\tau(V_M(p)).
$$

Valuation này mở rộng lên mọi công thức bằng các truth-functions trên FOUR. Ta ký hiệu kết quả là $V_M^\pi(\varphi)$.

## 3.3. Bổ đề đại số nền

**Bổ đề 3.1.** Với mọi $x,y\in[0,1]$, ta có:

$$
\mathbf 1[\min(x,y)\ge \tau]=\min(\mathbf 1[x\ge\tau],\mathbf 1[y\ge\tau]),
$$

$$
\mathbf 1[\max(x,y)\ge \tau]=\max(\mathbf 1[x\ge\tau],\mathbf 1[y\ge\tau]).
$$

**Chứng minh.**

Với biểu thức thứ nhất:

- nếu $\min(x,y)\ge\tau$, thì cả $x\ge\tau$ và $y\ge\tau$, nên hai indicator đều bằng 1, và vế phải bằng $\min(1,1)=1$;
- ngược lại, nếu $\min(x,y)<\tau$, thì ít nhất một trong hai số nhỏ hơn $\tau$, nên ít nhất một indicator bằng 0, và vế phải bằng 0.

Suy ra hai vế bằng nhau.

Với biểu thức thứ hai:

- nếu $\max(x,y)\ge\tau$, thì ít nhất một trong hai số vượt ngưỡng, nên ít nhất một indicator bằng 1, và vế phải bằng 1;
- nếu $\max(x,y)<\tau$, thì cả hai đều nhỏ hơn $\tau$, nên cả hai indicator đều bằng 0, và vế phải bằng 0.

Suy ra đẳng thức thứ hai. $\square$

## 3.4. Exact projection theorem

**Định lý 3.2.** Với mọi mô hình liên tục $M$ và mọi công thức $\varphi$,

$$
V_M^\pi(\varphi)=\pi_\tau(V_M(\varphi)).
$$

Nói cách khác: projection từ semantics liên tục xuống FOUR là **exact compositional projection**.

**Chứng minh.** Bằng quy nạp theo cấu trúc công thức.

**Cơ sở.** Nếu $\varphi=p$ là atom, thì theo định nghĩa

$$
V_M^\pi(p)=v_M^\pi(p)=\pi_\tau(V_M(p)).
$$

**Bước phủ định.** Giả sử mệnh đề đúng cho $\phi$. Khi đó:

$$
V_M^\pi(\neg\phi)=\neg V_M^\pi(\phi)=\neg\pi_\tau(V_M(\phi)).
$$

Vì $\neg$ trên cả hai miền chỉ là phép hoán đổi tọa độ, nên

$$
\neg\pi_\tau(V_M(\phi))=\pi_\tau(\neg V_M(\phi))=\pi_\tau(V_M(\neg\phi)).
$$

**Bước hội tụ.** Giả sử mệnh đề đúng cho $\phi$ và $\psi$. Khi đó:

$$
V_M^\pi(\phi\land\psi)=V_M^\pi(\phi)\land V_M^\pi(\psi).
$$

Theo giả thiết quy nạp,

$$
V_M^\pi(\phi)=\pi_\tau(V_M(\phi)),\qquad V_M^\pi(\psi)=\pi_\tau(V_M(\psi)).
$$

Viết $V_M(\phi)=(t_\phi,f_\phi)$, $V_M(\psi)=(t_\psi,f_\psi)$. Khi đó vế phải có tọa độ thứ nhất là

$$
\min\big(\mathbf 1[t_\phi\ge\tau],\mathbf 1[t_\psi\ge\tau]\big)=\mathbf 1[\min(t_\phi,t_\psi)\ge\tau]
$$

nhờ Bổ đề 3.1, và tọa độ thứ hai là

$$
\max\big(\mathbf 1[f_\phi\ge\tau],\mathbf 1[f_\psi\ge\tau]\big)=\mathbf 1[\max(f_\phi,f_\psi)\ge\tau].
$$

Đó chính là

$$
\pi_\tau\big(\min(t_\phi,t_\psi),\max(f_\phi,f_\psi)\big)=\pi_\tau(V_M(\phi\land\psi)).
$$

**Bước tuyển và bước hòa giải.** Hoàn toàn tương tự, dùng Bổ đề 3.1 cho cặp $\max,\min$ của $\lor$ và cặp $\min,\min$ của $\oplus$. $\square$

## 3.5. Hệ quả về bảo toàn signed truth

**Hệ quả 3.3.** Với mọi signed formula $S\varphi$,

$$
M\models S\varphi \iff v_M^\pi\models_{FOUR} S\varphi.
$$

**Chứng minh.** Theo Định lý 3.2, hai valuation cho cùng projected status của $\varphi$. Mỗi sign chỉ hỏi xem bit thứ nhất hoặc bit thứ hai có bằng 1 hay 0 hay không. $\square$

# 4. Four-signed analytic calculus

## 4.1. Nhánh và tính thỏa mãn của nhánh

Một **nhánh** $B$ là một tập hữu hạn các signed formulas. Một valuation FOUR $v$ **thỏa** nhánh $B$ nếu nó thỏa mọi signed formula trong $B$.

Một nhánh **đóng** nếu tồn tại công thức $\varphi$ sao cho một trong hai điều kiện xảy ra:

- $T^+\varphi\in B$ và $T^-\varphi\in B$, hoặc
- $F^+\varphi\in B$ và $F^-\varphi\in B$.

Một nhánh **mở** là nhánh không đóng.

## 4.2. Quy tắc phân rã

### Phủ định

- $T^+(\neg\varphi) \rightsquigarrow F^+\varphi$
- $T^-(\neg\varphi) \rightsquigarrow F^-\varphi$
- $F^+(\neg\varphi) \rightsquigarrow T^+\varphi$
- $F^-(\neg\varphi) \rightsquigarrow T^-\varphi$

### Hội tụ $\land$

- $T^+(\varphi\land\psi) \rightsquigarrow T^+\varphi,\;T^+\psi$
- $T^-(\varphi\land\psi) \rightsquigarrow T^-\varphi \mid T^-\psi$
- $F^+(\varphi\land\psi) \rightsquigarrow F^+\varphi \mid F^+\psi$
- $F^-(\varphi\land\psi) \rightsquigarrow F^-\varphi,\;F^-\psi$

### Tuyển $\lor$

- $T^+(\varphi\lor\psi) \rightsquigarrow T^+\varphi \mid T^+\psi$
- $T^-(\varphi\lor\psi) \rightsquigarrow T^-\varphi,\;T^-\psi$
- $F^+(\varphi\lor\psi) \rightsquigarrow F^+\varphi,\;F^+\psi$
- $F^-(\varphi\lor\psi) \rightsquigarrow F^-\varphi \mid F^-\psi$

### Hòa giải $\oplus$

- $T^+(\varphi\oplus\psi) \rightsquigarrow T^+\varphi,\;T^+\psi$
- $T^-(\varphi\oplus\psi) \rightsquigarrow T^-\varphi \mid T^-\psi$
- $F^+(\varphi\oplus\psi) \rightsquigarrow F^+\varphi,\;F^+\psi$
- $F^-(\varphi\oplus\psi) \rightsquigarrow F^-\varphi \mid F^-\psi$

Ký hiệu $\mid$ chỉ phân nhánh: nhánh mẹ được thay bằng hai nhánh con.

## 4.3. Nhánh bão hòa

Một nhánh mở $B$ gọi là **bão hòa** nếu mọi signed formula compound trong $B$ đã được phân rã theo một trong các điều kiện sau:

- với quy tắc không phân nhánh, tất cả signed subformulas kết quả đều đã nằm trong $B$;
- với quy tắc phân nhánh, ít nhất một nhánh con tương ứng đã được “chọn” vào $B$. Cụ thể:
  - nếu $T^-(\phi\land\psi)\in B$, thì $T^-\phi\in B$ hoặc $T^-\psi\in B$;
  - nếu $F^+(\phi\land\psi)\in B$, thì $F^+\phi\in B$ hoặc $F^+\psi\in B$;
  - nếu $T^+(\phi\lor\psi)\in B$, thì $T^+\phi\in B$ hoặc $T^+\psi\in B$;
  - nếu $F^-(\phi\lor\psi)\in B$, thì $F^-\phi\in B$ hoặc $F^-\psi\in B$;
  - nếu $T^-(\phi\oplus\psi)\in B$, thì $T^-\phi\in B$ hoặc $T^-\psi\in B$;
  - nếu $F^-(\phi\oplus\psi)\in B$, thì $F^-\phi\in B$ hoặc $F^-\psi\in B$.

Khái niệm này chính là phiên bản Nullivance của một **Hintikka branch**.

# 5. Soundness cục bộ và global soundness

## 5.1. Soundness cục bộ cho phủ định

**Bổ đề 5.1.** Mỗi quy tắc phủ định bảo toàn tính thỏa mãn theo hai chiều.

**Chứng minh.** Ta làm mẫu với $T^+(\neg\phi)$.

Theo semantics,

$$
V(\neg\phi)=(f(\phi),t(\phi)).
$$

Do đó:

$$
v\models T^+(\neg\phi)
\iff \text{tọa độ thứ nhất của }V(\neg\phi)=1
\iff \text{tọa độ thứ hai của }V(\phi)=1
\iff v\models F^+\phi.
$$

Ba trường hợp còn lại hoàn toàn tương tự. $\square$

## 5.2. Soundness cục bộ cho $\land$

**Bổ đề 5.2.** Các quy tắc cho $\land$ là locally sound.

**Chứng minh.**

1. $T^+(\phi\land\psi)\rightsquigarrow T^+\phi,T^+\psi$.

Ta có

$$
v\models T^+(\phi\land\psi)
\iff \min(t(\phi),t(\psi))=1
\iff t(\phi)=1 \text{ và } t(\psi)=1
\iff v\models T^+\phi \text{ và } v\models T^+\psi.
$$

2. $T^-(\phi\land\psi)\rightsquigarrow T^-\phi\mid T^-\psi$.

$$
v\models T^-(\phi\land\psi)
\iff \min(t(\phi),t(\psi))=0
\iff t(\phi)=0 \text{ hoặc } t(\psi)=0.
$$

Vậy một valuation thỏa nhánh mẹ khi và chỉ khi nó thỏa ít nhất một trong hai nhánh con.

3. $F^+(\phi\land\psi)\rightsquigarrow F^+\phi\mid F^+\psi$.

$$
v\models F^+(\phi\land\psi)
\iff \max(f(\phi),f(\psi))=1
\iff f(\phi)=1 \text{ hoặc } f(\psi)=1.
$$

4. $F^-(\phi\land\psi)\rightsquigarrow F^-\phi,F^-\psi$.

$$
v\models F^-(\phi\land\psi)
\iff \max(f(\phi),f(\psi))=0
\iff f(\phi)=0 \text{ và } f(\psi)=0.
$$

Suy ra mọi quy tắc cho $\land$ đều locally sound. $\square$

## 5.3. Soundness cục bộ cho $\lor$

**Bổ đề 5.3.** Các quy tắc cho $\lor$ là locally sound.

**Chứng minh.**

1. $T^+(\phi\lor\psi)\rightsquigarrow T^+\phi\mid T^+\psi$.

$$
v\models T^+(\phi\lor\psi)
\iff \max(t(\phi),t(\psi))=1
\iff t(\phi)=1 \text{ hoặc } t(\psi)=1.
$$

2. $T^-(\phi\lor\psi)\rightsquigarrow T^-\phi,T^-\psi$.

$$
v\models T^-(\phi\lor\psi)
\iff \max(t(\phi),t(\psi))=0
\iff t(\phi)=0 \text{ và } t(\psi)=0.
$$

3. $F^+(\phi\lor\psi)\rightsquigarrow F^+\phi,F^+\psi$.

$$
v\models F^+(\phi\lor\psi)
\iff \min(f(\phi),f(\psi))=1
\iff f(\phi)=1 \text{ và } f(\psi)=1.
$$

4. $F^-(\phi\lor\psi)\rightsquigarrow F^-\phi\mid F^-\psi$.

$$
v\models F^-(\phi\lor\psi)
\iff \min(f(\phi),f(\psi))=0
\iff f(\phi)=0 \text{ hoặc } f(\psi)=0.
$$

Suy ra kết luận. $\square$

## 5.4. Soundness cục bộ cho $\oplus$

**Bổ đề 5.4.** Các quy tắc cho $\oplus$ là locally sound.

**Chứng minh.** Vì cả hai kênh của $\oplus$ đều dùng $\min$, ta có ngay:

$$
v\models T^+(\phi\oplus\psi)
\iff t(\phi)=1 \text{ và } t(\psi)=1,
$$

$$
v\models T^-(\phi\oplus\psi)
\iff t(\phi)=0 \text{ hoặc } t(\psi)=0,
$$

$$
v\models F^+(\phi\oplus\psi)
\iff f(\phi)=1 \text{ và } f(\psi)=1,
$$

$$
v\models F^-(\phi\oplus\psi)
\iff f(\phi)=0 \text{ hoặc } f(\psi)=0.
$$

Đó chính là nội dung của bốn quy tắc phân rã. $\square$

## 5.5. Định lý soundness toàn cục

**Định lý 5.5.** Nếu một tableau xây từ nhánh đầu $B_0$ đóng hoàn toàn, thì $B_0$ không thỏa được trong FOUR matrix semantics.

**Chứng minh.**

- Mỗi quy tắc không phân nhánh thay nhánh mẹ bằng một nhánh con thỏa mãn đúng cùng lớp valuation.
- Mỗi quy tắc phân nhánh thay nhánh mẹ bằng hai nhánh con sao cho nhánh mẹ thỏa được khi và chỉ khi ít nhất một nhánh con thỏa được.
- Một nhánh đóng không thỏa được, vì không valuation nào có thể vừa làm bit truth bằng 1 vừa bằng 0 cho cùng một công thức; tương tự cho bit falsity.

Suy ra, nếu tất cả lá của tableau đều đóng, thì không còn valuation nào thỏa nhánh gốc $B_0$. $\square$

# 6. Tính dừng và cấu trúc hữu hạn của proof search

## 6.1. Subformula property

**Bổ đề 6.1.** Mọi signed formula được sinh ra trong một tableau từ $B_0$ đều có dạng $S\psi$, trong đó $\psi$ là một subformula của một công thức trong $B_0$.

**Chứng minh.** Hiển nhiên từ bảng quy tắc: mỗi lần phân rã chỉ sinh ra signed subformulas trực tiếp của công thức đang xét. Lặp lại hữu hạn lần thì chỉ đi xuống cây subformula. $\square$

## 6.2. Hữu hạn hóa nhánh

**Bổ đề 6.2.** Nếu xem mỗi nhánh là một **tập** signed formulas và không thêm lại công thức đã có sẵn, thì trên mỗi nhánh chỉ có hữu hạn nhiều signed formulas có thể xuất hiện.

**Chứng minh.** Nếu $Sub(B_0)$ là tập các subformulas của tất cả công thức ở nhánh gốc, thì số signed formulas khả dĩ nhiều nhất là

$$
4\cdot |Sub(B_0)|,
$$

vì mỗi subformula chỉ có bốn sign khả dĩ. $\square$

## 6.3. Tính dừng

**Định lý 6.3.** Với chiến lược công bằng và quy ước “không phân rã lại một công thức đã xử lý”, mọi proof search từ một nhánh đầu hữu hạn đều kết thúc bằng một tableau hữu hạn mà mọi lá hoặc đóng, hoặc mở và bão hòa.

**Chứng minh.** Theo Bổ đề 6.2, trên mỗi nhánh có hữu hạn nhiều signed formulas khả dĩ. Mỗi lần mở rộng xử lý ít nhất một signed formula chưa phân rã. Vì vậy trên mỗi nhánh chỉ có hữu hạn bước. Số nhánh cũng hữu hạn vì mỗi lần phân nhánh chỉ tạo đúng hai nhánh con từ một công thức chưa xử lý, mà số công thức chưa xử lý là hữu hạn. Do đó toàn bộ cây proof search là hữu hạn. Khi thuật toán dừng, mỗi lá hoặc đóng, hoặc không còn công thức nào chưa phân rã; trường hợp thứ hai chính là mở và bão hòa. $\square$

# 7. Canonical valuation cho open saturated branch

## 7.1. Định nghĩa valuation chuẩn tắc

Cho $B$ là một nhánh mở và bão hòa. Với mỗi atom $p$, đặt:

$$
x_B(p)=\begin{cases}
1 & \text{nếu } T^+p\in B,\\
0 & \text{nếu không.}
\end{cases}
$$

$$
y_B(p)=\begin{cases}
1 & \text{nếu } F^+p\in B,\\
0 & \text{nếu không.}
\end{cases}
$$

và định nghĩa

$$
v_B(p)=(x_B(p),y_B(p))\in FOUR.
$$

Valuation này mở rộng lên mọi công thức bằng các truth-functions FOUR.

## 7.2. Bổ đề nguyên tử

**Bổ đề 7.1.** Với mọi atom $p$:

- nếu $T^+p\in B$ thì bit truth của $v_B(p)$ bằng 1;
- nếu $T^-p\in B$ thì bit truth của $v_B(p)$ bằng 0;
- nếu $F^+p\in B$ thì bit falsity của $v_B(p)$ bằng 1;
- nếu $F^-p\in B$ thì bit falsity của $v_B(p)$ bằng 0.

**Chứng minh.** Hai mệnh đề với dấu cộng là đúng theo định nghĩa của $v_B$. Với dấu trừ, dùng tính mở của nhánh: nếu $T^-p\in B$ mà bit truth của $v_B(p)$ lại bằng 1, thì phải có $T^+p\in B$, làm nhánh đóng. Mâu thuẫn. Lập luận cho $F^-p$ hoàn toàn tương tự. $\square$

# 8. Truth Lemma chi tiết

**Định lý 8.1 (Truth Lemma).** Cho $B$ là một nhánh mở và bão hòa, và $v_B$ là canonical valuation ở trên. Với mọi công thức $\varphi$:

1. nếu $T^+\varphi\in B$ thì $v_B\models T^+\varphi$;
2. nếu $T^-\varphi\in B$ thì $v_B\models T^-\varphi$;
3. nếu $F^+\varphi\in B$ thì $v_B\models F^+\varphi$;
4. nếu $F^-\varphi\in B$ thì $v_B\models F^-\varphi$.

**Chứng minh.** Quy nạp theo độ phức tạp của $\varphi$.

### Cơ sở: $\varphi=p$ là atom

Đúng theo Bổ đề 7.1.

### Bước phủ định: $\varphi=\neg\phi$

- Nếu $T^+\neg\phi\in B$, vì nhánh bão hòa nên $F^+\phi\in B$. Theo giả thiết quy nạp, bit falsity của $V_{v_B}(\phi)$ bằng 1. Do $\neg$ hoán đổi hai bit, bit truth của $V_{v_B}(\neg\phi)$ bằng 1. Vậy $v_B\models T^+\neg\phi$.
- Nếu $T^-\neg\phi\in B$, nhánh bão hòa cho $F^-\phi\in B$. Theo giả thiết quy nạp, bit falsity của $\phi$ bằng 0. Sau phép swap, bit truth của $\neg\phi$ bằng 0. Vậy $v_B\models T^-\neg\phi$.
- Nếu $F^+\neg\phi\in B$, nhánh bão hòa cho $T^+\phi\in B$. Theo giả thiết quy nạp, bit truth của $\phi$ bằng 1, nên bit falsity của $\neg\phi$ bằng 1.
- Nếu $F^-\neg\phi\in B$, nhánh bão hòa cho $T^-\phi\in B$. Theo giả thiết quy nạp, bit truth của $\phi$ bằng 0, nên bit falsity của $\neg\phi$ bằng 0.

### Bước hội tụ: $\varphi=\phi\land\psi$

- Nếu $T^+(\phi\land\psi)\in B$, do bão hòa nên $T^+\phi\in B$ và $T^+\psi\in B$. Theo giả thiết quy nạp, hai bit truth đều bằng 1. Vậy
  $$
  \min(t(\phi),t(\psi))=1,
  $$
  nên $v_B\models T^+(\phi\land\psi)$.

- Nếu $T^-(\phi\land\psi)\in B$, do bão hòa nên $T^-\phi\in B$ hoặc $T^-\psi\in B$. Theo giả thiết quy nạp, một trong hai bit truth bằng 0. Vậy
  $$
  \min(t(\phi),t(\psi))=0,
  $$
  nên $v_B\models T^-(\phi\land\psi)$.

- Nếu $F^+(\phi\land\psi)\in B$, do bão hòa nên $F^+\phi\in B$ hoặc $F^+\psi\in B$. Theo giả thiết quy nạp, một trong hai bit falsity bằng 1. Do falsity của $\land$ dùng $\max$, ta được
  $$
  \max(f(\phi),f(\psi))=1.
  $$

- Nếu $F^-(\phi\land\psi)\in B$, do bão hòa nên $F^-\phi\in B$ và $F^-\psi\in B$. Theo giả thiết quy nạp, cả hai bit falsity đều bằng 0. Vì vậy
  $$
  \max(f(\phi),f(\psi))=0.
  $$

### Bước tuyển: $\varphi=\phi\lor\psi$

- Nếu $T^+(\phi\lor\psi)\in B$, do bão hòa nên $T^+\phi\in B$ hoặc $T^+\psi\in B$. Theo giả thiết quy nạp, một trong hai bit truth bằng 1. Vì truth của $\lor$ dùng $\max$, suy ra $v_B\models T^+(\phi\lor\psi)$.

- Nếu $T^-(\phi\lor\psi)\in B$, do bão hòa nên $T^-\phi\in B$ và $T^-\psi\in B$. Theo giả thiết quy nạp, cả hai bit truth đều bằng 0. Khi đó $\max(t(\phi),t(\psi))=0$.

- Nếu $F^+(\phi\lor\psi)\in B$, do bão hòa nên $F^+\phi\in B$ và $F^+\psi\in B$. Theo giả thiết quy nạp, cả hai bit falsity bằng 1. Vì falsity của $\lor$ dùng $\min$, ta được $\min(f(\phi),f(\psi))=1$.

- Nếu $F^-(\phi\lor\psi)\in B$, do bão hòa nên $F^-\phi\in B$ hoặc $F^-\psi\in B$. Theo giả thiết quy nạp, một trong hai bit falsity bằng 0. Khi đó $\min(f(\phi),f(\psi))=0$.

### Bước hòa giải: $\varphi=\phi\oplus\psi$

- Nếu $T^+(\phi\oplus\psi)\in B$, do bão hòa nên $T^+\phi\in B$ và $T^+\psi\in B$. Suy ra $\min(t(\phi),t(\psi))=1$.

- Nếu $T^-(\phi\oplus\psi)\in B$, do bão hòa nên $T^-\phi\in B$ hoặc $T^-\psi\in B$. Suy ra $\min(t(\phi),t(\psi))=0$.

- Nếu $F^+(\phi\oplus\psi)\in B$, do bão hòa nên $F^+\phi\in B$ và $F^+\psi\in B$. Suy ra $\min(f(\phi),f(\psi))=1$.

- Nếu $F^-(\phi\oplus\psi)\in B$, do bão hòa nên $F^-\phi\in B$ hoặc $F^-\psi\in B$. Suy ra $\min(f(\phi),f(\psi))=0$.

Mọi trường hợp đều đúng; định lý được chứng minh. $\square$

## 8.2. Hệ quả: open saturated branch luôn thỏa được

**Hệ quả 8.2.** Mọi nhánh mở và bão hòa đều thỏa được trong FOUR matrix semantics.

**Chứng minh.** Theo Định lý 8.1, canonical valuation $v_B$ thỏa mọi signed formula trong $B$. $\square$

# 9. Completeness trên FOUR matrix

## 9.1. Dạng phát biểu branch-completeness

**Định lý 9.1 (FOUR branch-completeness).** Với mọi nhánh đầu hữu hạn $B_0$, mọi tableau công bằng và mở rộng đầy đủ từ $B_0$ có tính chất:

- hoặc mọi lá đều đóng,
- hoặc tồn tại một lá mở và bão hòa, nên $B_0$ thỏa được.

Hệ quả tương đương là:

$$
B_0 \text{ không thỏa được } \iff \text{mọi tableau đầy đủ từ } B_0 \text{ đều đóng.}
$$

**Chứng minh.** Theo Định lý 6.3, proof search dừng ở một tableau hữu hạn mà mọi lá hoặc đóng, hoặc mở và bão hòa. Nếu có một lá mở và bão hòa, thì theo Hệ quả 8.2 lá đó thỏa được; mà local soundness cho biết tính thỏa được của lá lan ngược về gốc. Vậy $B_0$ thỏa được. Ngược lại, nếu mọi lá đều đóng, thì theo Định lý 5.5 nhánh gốc không thỏa được. $\square$

## 9.2. Signed entailment completeness

Ta định nghĩa signed consequence trên FOUR như sau. Với tập signed premises $\Sigma$ và signed conclusion $S\varphi$:

$$
\Sigma \models_{FOUR} S\varphi
$$

nghĩa là mọi valuation FOUR thỏa toàn bộ $\Sigma$ đều thỏa $S\varphi$.

Ta cũng định nghĩa tableau-derivability:

$$
\Sigma \vdash_{A} S\varphi
$$

nghĩa là tableau khởi đầu từ

$$
B_0=\Sigma\cup\{\overline{S\varphi}\}
$$

đóng hoàn toàn.

**Định lý 9.2 (Soundness và completeness của calculus trên FOUR).** Với mọi $\Sigma$ hữu hạn và mọi signed conclusion $S\varphi$,

$$
\Sigma \vdash_A S\varphi \iff \Sigma \models_{FOUR} S\varphi.
$$

**Chứng minh.**

- $(\Rightarrow)$ Nếu tableau của $\Sigma\cup\{\overline{S\varphi}\}$ đóng, thì theo Định lý 5.5 không valuation FOUR nào thỏa cả premises lẫn phủ định của kết luận. Vì vậy mọi valuation thỏa $\Sigma$ đều thỏa $S\varphi$.

- $(\Leftarrow)$ Giả sử $\Sigma\not\vdash_A S\varphi$. Khi đó tồn tại một tableau đầy đủ của $\Sigma\cup\{\overline{S\varphi}\}$ không đóng hoàn toàn. Theo Định lý 9.1, có một lá mở và bão hòa, nên có valuation FOUR thỏa $\Sigma\cup\{\overline{S\varphi}\}$. Valuation đó thỏa $\Sigma$ nhưng không thỏa $S\varphi$. Do đó $\Sigma\not\models_{FOUR} S\varphi$.

Suy ra hai chiều tương đương. $\square$

# 10. Lifting theorem: từ FOUR về continuous NPL

## 10.1. Satisfiability equivalence

**Định lý 10.1.** Một nhánh hữu hạn $B$ thỏa được trong semantics liên tục của NPL khi và chỉ khi nó thỏa được trong FOUR matrix semantics.

**Chứng minh.**

**Chiều $(\Rightarrow)$.** Giả sử có mô hình liên tục $M$ thỏa $B$. Theo Hệ quả 3.3, projected valuation $v_M^\pi$ trên FOUR thỏa chính cùng các signed formulas. Vậy $B$ thỏa được trên FOUR.

**Chiều $(\Leftarrow)$.** Giả sử có valuation FOUR $v$ thỏa $B$. Ta dựng một mô hình liên tục $M_v$ bằng cách gán cho mỗi atom đúng cặp số thực tương ứng với trạng thái FOUR đó:

$$
T\mapsto (1,0),\quad F\mapsto (0,1),\quad B\mapsto (1,1),\quad N\mapsto (0,0).
$$

Các cặp này đều nằm trong $[0,1]^2$. Vì các connective của NPL liên tục và của FOUR đều dùng cùng các phép $\min,\max,\text{swap}$, nên trên mọi công thức ta nhận đúng cùng cặp bit 0/1. Do đó signed truth của mọi công thức được bảo toàn. Vậy $M_v$ thỏa $B$. $\square$

## 10.2. Completeness cho semantics liên tục

**Định lý 10.2 (Completeness của four-signed analytic calculus cho NPL liên tục).** Với mọi $\Sigma$ hữu hạn và signed conclusion $S\varphi$,

$$
\Sigma \vdash_A S\varphi \iff \Sigma \models_{cont} S\varphi.
$$

**Chứng minh.**

- Soundness: nếu tableau đóng thì nhánh khởi đầu không thỏa được trên FOUR theo Định lý 5.5, và do Định lý 10.1 nó cũng không thỏa được trên semantics liên tục. Vậy mọi continuous model thỏa $\Sigma$ đều thỏa $S\varphi$.

- Completeness: nếu $\Sigma\not\vdash_A S\varphi$, thì theo Định lý 9.2 có valuation FOUR thỏa $\Sigma\cup\{\overline{S\varphi}\}$. Theo Định lý 10.1 valuation này nâng thành continuous model thỏa đúng nhánh đó. Vậy $\Sigma\not\models_{cont} S\varphi$.

Suy ra tương đương. $\square$

# 11. Các hệ quả quan trọng cho Nullivance

## 11.1. Bảo tồn unsigned NPL cũ

**Hệ quả 11.1.** Với mọi tập công thức unsigned $\Gamma$ và công thức $\varphi$,

$$
\Gamma\models_{old}\varphi
\iff
\{T^+\gamma: \gamma\in\Gamma\}\models_{cont}T^+\varphi.
$$

**Chứng minh.** Theo định nghĩa của unsigned reading cũ, $M\models_{old}\chi$ đúng khi và chỉ khi $M\models T^+\chi$. $\square$

Điều này cho thấy NPL v2.0 là **conservative extension** của NPL cũ, không phải một logic thay thế.

## 11.2. Non-explosion

**Hệ quả 11.2.** Hệ NPL v2.0 là paraconsistent: nói chung

$$
\{T^+\phi, T^+(\neg\phi)\}\not\models T^+\psi.
$$

**Chứng minh.** Lấy valuation FOUR với $v(p)=B$ và $v(q)=N$. Khi đó $T^+p$ và $T^+(\neg p)$ đều đúng, nhưng $T^+q$ sai. $\square$

## 11.3. Vai trò chính xác của $\oplus$

**Hệ quả 11.3.** Với mọi $\phi,\psi$, ta có

$$
T^+(\phi\oplus\psi) \iff T^+(\phi\land\psi),
$$

nhưng không có tương đương tổng quát

$$
F^+(\phi\oplus\psi) \iff F^+(\phi\land\psi).
$$

**Chứng minh.** Truth-coordinate của cả $\land$ lẫn $\oplus$ đều là $\min$, nên tương đương đầu tiên hiển nhiên. Với vế thứ hai, lấy $v(p)=T$, $v(q)=F$. Khi đó

$$
p\land q = F,\qquad p\oplus q = N,
$$

nên $F^+(p\land q)$ đúng còn $F^+(p\oplus q)$ sai. $\square$

Đây là cách phát biểu chính xác nhất của nguyên lý harmonization trong Nullivance: $\oplus$ đồng ý với $\land$ ở truth-channel, nhưng không tích lũy falsity đơn phương.

# 12. Kết luận và giới hạn hiện tại

Bản chứng minh này hoàn tất phần logic cốt lõi mà các bản trước mới dừng ở mức roadmap:

1. Projection từ $[0,1]^2$ xuống FOUR không chỉ là một trực giác density, mà là một phép chiếu cấu trúc chính xác.
2. Four-signed analytic calculus là sound và complete cho projected matrix semantics.
3. Continuous NPL thừa hưởng completeness đó qua lifting theorem.
4. Unsigned Nullivance cũ được giữ nguyên như positive projection của hệ mới.

Giới hạn còn lại không nằm ở formal entailment nữa, mà nằm ở các tầng cao hơn:

- cơ chế pattern emergence toàn cục;
- mối quan hệ giữa latent field và proof theory;
- phiên bản có lượng hóa hoặc thời gian;
- và khả năng machine-check các chứng minh trên trong Lean/Coq/Isabelle.

Nói ngắn: về mặt logic mệnh đề, NPL v2.0 hiện đã có một lõi completeness khá hoàn chỉnh ở mức paper mathematics. Bước kế tiếp hợp lý nhất là **chuẩn hóa phần này thành phiên bản nộp bài**, rồi tách một bài riêng cho latent/quasivance field.
