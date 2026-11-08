# Bản tổng hợp Nullivance đến DR-0149 — 08-11-2026

## Đọc từ đây

- Báo cáo tổng hợp tiếng Anh: [main.pdf](papers/npl-research-2026/main.pdf).
- Giải thích dễ hiểu bằng tiếng Việt: [TOM_TAT_VI.md](papers/npl-research-2026/TOM_TAT_VI.md).
- Bảng kiểm toán phát biểu–giả thiết–Lean: [claim-review.md](papers/npl-research-2026/claim-review.md).
- Hướng dẫn dựng lại và đóng gói: [README](papers/npl-research-2026/README.md).
- Mục lục 149 bản ghi: [catalog.json](papers/npl-research-2026/catalog.json).

Đây là bản tổng hợp mới của mốc toán học
`48bd5f4260fd7982176d7a2060be4e956e1fd49c`, không thay ngầm hai bài v0.7.1
đã lưu trước đó. Không thay đổi tiên đề hay các định nghĩa/chứng minh gốc.
Không tuyên bố đã hoàn chỉnh toàn bộ logic lượng từ vô hạn hoặc lý thuyết
nhận thức. Giả thiết, phản ví dụ và các nghĩa vụ còn mở được trình bày riêng.

Theo chỉ dẫn mới nhất của tác giả: **chỉ tổng hợp, kiểm tra và lưu trữ nội bộ;
không đăng aiXiv, không nộp bài, không push hay phát hành bên ngoài.**

## Tái lập

Tại thư mục gốc dự án:

```powershell
pwsh -NoProfile -File scripts/Verify-ResearchPublication.ps1
```

Log sinh ở `output/publication-dr0149/`. Gói nguồn được tạo trong `dist/`, có
SHA-256 cho từng tệp và cho ZIP. Gói là ảnh chụp nghiên cứu có thể tái lập;
không thay thế kho Git và các bản sao lưu đầy đủ của dự án.
