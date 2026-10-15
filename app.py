# -*- coding: utf-8 -*-
"""Quản lý khách hàng ngân hàng - bản Streamlit.
Chạy:  pip install streamlit pandas
       streamlit run app.py
"""
import csv
import heapq
import random
import re
import unicodedata
from datetime import date, timedelta

# ============================================================================
# PHẦN 1: LÕI CẤU TRÚC DỮ LIỆU & GIẢI THUẬT (lấy từ notebook)
# ============================================================================

def bo_dau(s):
    """'Nguyễn Văn Ân' -> 'nguyen van an' (để tìm kiếm không phân biệt dấu)."""
    s = s.replace("đ", "d").replace("Đ", "D")
    s = unicodedata.normalize("NFD", s)
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    return " ".join(s.lower().split())

EMAIL_RE = re.compile(r"^[\w.+-]+@[\w-]+(\.[\w-]+)+$")
LOAI_HOP_LE = ["Thường", "VIP", "Doanh nghiệp"]


class TrieNode:
    __slots__ = ("con", "ds_ma")
    def __init__(self):
        self.con = {}       # ký tự -> TrieNode
        self.ds_ma = set()  # mã KH đi qua nút này


class Trie:
    """Cây tiền tố: tìm mã KH có họ tên bắt đầu bằng một tiền tố, O(L)."""
    def __init__(self):
        self.goc = TrieNode()

    def chen(self, khoa, ma_kh):
        nut = self.goc
        for ch in khoa:
            nut = nut.con.setdefault(ch, TrieNode())
            nut.ds_ma.add(ma_kh)

    def xoa(self, khoa, ma_kh):
        nut = self.goc
        for ch in khoa:
            if ch not in nut.con:
                return
            nut = nut.con[ch]
            nut.ds_ma.discard(ma_kh)

    def tim_tien_to(self, tien_to):
        nut = self.goc
        for ch in tien_to:
            if ch not in nut.con:
                return set()
            nut = nut.con[ch]
        return set(nut.ds_ma)


def sap_xep_tron(ds, key, reverse=False):
    """Merge Sort tự cài đặt, ổn định, O(n log n); trả về danh sách MỚI."""
    if len(ds) <= 1:
        return list(ds)
    giua = len(ds) // 2
    trai = sap_xep_tron(ds[:giua], key, reverse)
    phai = sap_xep_tron(ds[giua:], key, reverse)
    kq, i, j = [], 0, 0
    while i < len(trai) and j < len(phai):
        a, b = key(trai[i]), key(phai[j])
        lay_trai = (a >= b) if reverse else (a <= b)
        if lay_trai:
            kq.append(trai[i]); i += 1
        else:
            kq.append(phai[j]); j += 1
    kq.extend(trai[i:])
    kq.extend(phai[j:])
    return kq


class QuanLyKhachHang:
    TRUONG = ["ma_kh", "ho_ten", "cccd", "sdt", "email", "dia_phuong", "loai_kh", "so_du", "ngay_dk"]

    def __init__(self):
        self.ds = []                                         # list
        self.chi_muc = {}                                    # dict: ma_kh -> hồ sơ
        self.tap_cccd, self.tap_sdt, self.tap_email = set(), set(), set()   # set
        self.trie = Trie()                                   # trie
        self.ngan_xep = []                                   # stack (Undo)

    def __len__(self):
        return len(self.ds)

    @staticmethod
    def chuan_hoa(rec):
        r = dict(rec)
        r["ma_kh"] = str(r.get("ma_kh", "")).strip().upper()
        r["ho_ten"] = " ".join(str(r.get("ho_ten", "")).split())
        r["cccd"] = str(r.get("cccd", "")).strip()
        r["sdt"] = str(r.get("sdt", "")).strip()
        r["email"] = str(r.get("email", "")).strip().lower()
        r["dia_phuong"] = str(r.get("dia_phuong", "")).strip()
        r["loai_kh"] = str(r.get("loai_kh", "")).strip()
        try:
            r["so_du"] = float(r.get("so_du"))
        except (TypeError, ValueError):
            r["so_du"] = None
        return r

    def kiem_tra_hop_le(self, r):
        for tr in self.TRUONG:
            if tr not in r or r[tr] is None or r[tr] == "":
                return False, f"Thiếu hoặc sai trường '{tr}'"
        if not (len(r["cccd"]) == 12 and r["cccd"].isdigit()):
            return False, "CCCD phải gồm 12 chữ số"
        if not (len(r["sdt"]) == 10 and r["sdt"].isdigit() and r["sdt"].startswith("0")):
            return False, "SĐT phải gồm 10 chữ số, bắt đầu bằng 0"
        if not EMAIL_RE.match(r["email"]):
            return False, "Email không đúng định dạng"
        if r["loai_kh"] not in LOAI_HOP_LE:
            return False, "Loại khách hàng không hợp lệ"
        if r["so_du"] < 0:
            return False, "Số dư không được âm"
        return True, ""

    def _kiem_tra_trung(self, r, bo_qua_ma=None):
        if r["ma_kh"] in self.chi_muc and r["ma_kh"] != bo_qua_ma:
            return "Trùng mã khách hàng"
        cu = self.chi_muc.get(bo_qua_ma) if bo_qua_ma else None
        if r["cccd"] in self.tap_cccd and (not cu or r["cccd"] != cu["cccd"]):
            return "Trùng CCCD"
        if r["sdt"] in self.tap_sdt and (not cu or r["sdt"] != cu["sdt"]):
            return "Trùng số điện thoại"
        if r["email"] in self.tap_email and (not cu or r["email"] != cu["email"]):
            return "Trùng email"
        return ""

    def _chi_muc_hoa(self, r):
        self.chi_muc[r["ma_kh"]] = r
        self.tap_cccd.add(r["cccd"])
        self.tap_sdt.add(r["sdt"])
        self.tap_email.add(r["email"])
        tu = bo_dau(r["ho_ten"]).split()
        for i in range(len(tu)):
            self.trie.chen(" ".join(tu[i:]), r["ma_kh"])

    def _go_chi_muc(self, r):
        self.chi_muc.pop(r["ma_kh"], None)
        self.tap_cccd.discard(r["cccd"])
        self.tap_sdt.discard(r["sdt"])
        self.tap_email.discard(r["email"])
        tu = bo_dau(r["ho_ten"]).split()
        for i in range(len(tu)):
            self.trie.xoa(" ".join(tu[i:]), r["ma_kh"])

    def them(self, rec, ghi_undo=True):
        r = self.chuan_hoa(rec)
        ok, ly_do = self.kiem_tra_hop_le(r)
        if not ok:
            return False, ly_do
        ly_do = self._kiem_tra_trung(r)
        if ly_do:
            return False, ly_do
        self.ds.append(r)
        self._chi_muc_hoa(r)
        if ghi_undo:
            self.ngan_xep.append(("them", r["ma_kh"]))
        return True, "Đã thêm khách hàng " + r["ma_kh"]

    def tra_cuu(self, ma_kh):
        return self.chi_muc.get(str(ma_kh).strip().upper())

    def tim_theo_ten(self, tien_to):
        tien_to = bo_dau(str(tien_to))
        if not tien_to:
            return []
        tap_ma = self.trie.tim_tien_to(tien_to)
        return [self.chi_muc[m] for m in sorted(tap_ma) if m in self.chi_muc]

    def sua(self, ma_kh, **thay_doi):
        ma_kh = str(ma_kh).strip().upper()
        cu = self.chi_muc.get(ma_kh)
        if cu is None:
            return False, "Không tìm thấy khách hàng"
        thay_doi.pop("ma_kh", None)
        moi = self.chuan_hoa({**cu, **thay_doi})
        ok, ly_do = self.kiem_tra_hop_le(moi)
        if not ok:
            return False, ly_do
        ly_do = self._kiem_tra_trung(moi, bo_qua_ma=ma_kh)
        if ly_do:
            return False, ly_do
        vi_tri = self.ds.index(cu)
        self._go_chi_muc(cu)
        self.ds[vi_tri] = moi
        self._chi_muc_hoa(moi)
        self.ngan_xep.append(("sua", dict(cu)))
        return True, "Đã cập nhật " + ma_kh

    def xoa(self, ma_kh, ghi_undo=True):
        ma_kh = str(ma_kh).strip().upper()
        cu = self.chi_muc.get(ma_kh)
        if cu is None:
            return False, "Không tìm thấy khách hàng"
        vi_tri = self.ds.index(cu)
        del self.ds[vi_tri]
        self._go_chi_muc(cu)
        if ghi_undo:
            self.ngan_xep.append(("xoa", dict(cu), vi_tri))
        return True, "Đã xóa " + ma_kh

    def hoan_tac(self):
        if not self.ngan_xep:
            return False, "Không còn thao tác để hoàn tác"
        thao_tac = self.ngan_xep.pop()
        if thao_tac[0] == "them":
            self.xoa(thao_tac[1], ghi_undo=False)
            return True, "Đã hoàn tác: thêm " + thao_tac[1]
        if thao_tac[0] == "xoa":
            _, r, vi_tri = thao_tac
            self.ds.insert(vi_tri, r)
            self._chi_muc_hoa(r)
            return True, "Đã hoàn tác: xóa " + r["ma_kh"]
        r = thao_tac[1]                                      # thao tác "sua"
        hien_tai = self.chi_muc[r["ma_kh"]]
        vi_tri = self.ds.index(hien_tai)
        self._go_chi_muc(hien_tai)
        self.ds[vi_tri] = r
        self._chi_muc_hoa(r)
        return True, "Đã hoàn tác: sửa " + r["ma_kh"]

    def sap_xep(self, theo="ho_ten", giam_dan=False, ds=None):
        nguon = self.ds if ds is None else ds
        if theo == "ho_ten":
            def khoa(kh):
                tu = bo_dau(kh["ho_ten"]).split()
                return (tu[-1], bo_dau(kh["ho_ten"]))       # xếp theo tên gọi rồi họ tên
        else:
            def khoa(kh):
                return kh[theo]
        return sap_xep_tron(nguon, khoa, giam_dan)

    def top_k_so_du(self, k):
        if k <= 0:
            return []
        return heapq.nlargest(k, self.ds, key=lambda kh: kh["so_du"])

    def thong_ke(self, theo="loai_kh"):
        nhom = {}
        for kh in self.ds:
            m = nhom.setdefault(kh[theo], {"so_luong": 0, "tong_so_du": 0.0})
            m["so_luong"] += 1
            m["tong_so_du"] += kh["so_du"]
        return nhom

    def ghi_csv(self, duong_dan):
        with open(duong_dan, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.DictWriter(f, fieldnames=self.TRUONG)
            w.writeheader()
            for kh in self.ds:
                row = dict(kh)
                row["ngay_dk"] = str(row["ngay_dk"])
                w.writerow(row)

    def doc_csv(self, duong_dan):
        them_duoc, loi = 0, []
        with open(duong_dan, newline="", encoding="utf-8-sig") as f:
            for dong, row in enumerate(csv.DictReader(f), start=2):
                try:
                    row["ngay_dk"] = date.fromisoformat(row["ngay_dk"])
                except (ValueError, KeyError):
                    loi.append((dong, "Ngày đăng ký không hợp lệ"))
                    continue
                ok, msg = self.them(row)
                if ok:
                    them_duoc += 1
                else:
                    loi.append((dong, msg))
        return them_duoc, loi


# --- Dữ liệu mô phỏng ---
HO = ["Nguyễn", "Trần", "Lê", "Phạm", "Hoàng", "Huỳnh", "Phan", "Vũ", "Võ", "Đặng", "Bùi", "Đỗ", "Hồ", "Ngô", "Dương"]
DEM = ["Văn", "Thị", "Minh", "Quốc", "Thanh", "Ngọc", "Hữu", "Anh", "Gia", "Thu", "Đức", "Hoài"]
TEN = ["An", "Bình", "Châu", "Dũng", "Giang", "Hà", "Hùng", "Khánh", "Lan", "Linh", "Mai", "Nam",
       "Phúc", "Quân", "Sơn", "Thảo", "Trang", "Tuấn", "Vy", "Yến", "Ân", "Đạt", "Oanh", "Hiếu"]
DIA_PHUONG = ["TP. Hồ Chí Minh", "Hà Nội", "Đà Nẵng", "Cần Thơ", "Hải Phòng",
              "Đồng Nai", "Bình Dương", "Khánh Hòa", "Lâm Đồng", "Nghệ An"]


def sinh_du_lieu(n, hat_giong=42):
    rd = random.Random(hat_giong)
    ds = []
    ngay_dau = date(2015, 1, 1)
    so_ngay = (date.today() - ngay_dau).days
    cccd_set = rd.sample(range(10**11, 10**12), n)
    sdt_set = rd.sample(range(10**8, 10**9), n)
    for i in range(n):
        ten = f"{rd.choice(HO)} {rd.choice(DEM)} {rd.choice(TEN)}"
        loai = rd.choices(LOAI_HOP_LE, weights=[80, 15, 5])[0]
        he_so = {"Thường": 1, "VIP": 8, "Doanh nghiệp": 25}[loai]
        so_du = round(rd.lognormvariate(16.0, 1.0) * he_so / 10) * 10
        ds.append({
            "ma_kh": f"KH{i + 1:06d}",
            "ho_ten": ten,
            "cccd": f"{cccd_set[i]:012d}",
            "sdt": f"0{sdt_set[i]:09d}",
            "email": f"{bo_dau(ten).replace(' ', '.')}.{i + 1}@mail.test",
            "dia_phuong": rd.choice(DIA_PHUONG),
            "loai_kh": loai,
            "so_du": float(so_du),
            "ngay_dk": ngay_dau + timedelta(days=rd.randrange(so_ngay)),
        })
    return ds


def nap_he_thong(ds):
    ql = QuanLyKhachHang()
    for r in ds:
        ql.them(r, ghi_undo=False)
    return ql


def vnd(x):
    return f"{x:,.0f}".replace(",", ".")



# ============================================================================
# PHẦN 2: GIAO DIỆN WEB (Streamlit)
# ============================================================================
import streamlit as st
import pandas as pd
import io

st.set_page_config(page_title="Quản lý khách hàng ngân hàng", page_icon="🏦", layout="wide")

st.markdown("""
<style>
.block-container {padding-top: 1.5rem;}
h1, h2, h3 {color: #0b5d5b;}
div[data-testid="stMetric"] {background: #f1f7f6; border-left: 4px solid #0b8a84;
    padding: 10px 14px; border-radius: 8px;}
</style>""", unsafe_allow_html=True)

CODE_COT = {"ma_kh": "Mã KH", "ho_ten": "Họ tên", "cccd": "CCCD", "sdt": "SĐT",
            "email": "Email", "dia_phuong": "Địa phương", "loai_kh": "Loại KH",
            "so_du": "Số dư (VND)", "ngay_dk": "Ngày ĐK"}

# session_state giữ dữ liệu giữa các lần Streamlit chạy lại script
if "ql" not in st.session_state:
    st.session_state.ql = nap_he_thong(sinh_du_lieu(1000))
ql = st.session_state.ql


def bang(ds):
    df = pd.DataFrame(ds, columns=list(CODE_COT))
    df["ngay_dk"] = df["ngay_dk"].astype(str)
    return df.rename(columns=CODE_COT)


def bao(kq):
    ok, msg = kq
    (st.success if ok else st.error)(msg)


# ---------------- Thanh bên ----------------
with st.sidebar:
    st.title("🏦 Ngân hàng")
    st.caption("Đề tài 6 – Cấu trúc dữ liệu tài chính & giải thuật")
    st.metric("Tổng khách hàng", len(ql))
    st.metric("Thao tác có thể hoàn tác", len(ql.ngan_xep))
    if st.button("↩️ Hoàn tác (Stack)", width="stretch"):
        bao(ql.hoan_tac())
        st.rerun()
    st.divider()
    st.markdown("**Cấu trúc dữ liệu**  \nlist · dict · set · Trie · Merge Sort · Heap · Stack")

st.title("Quản lý thông tin khách hàng ngân hàng")
tab_ds, tab_them, tab_tk, tab_top, tab_csv = st.tabs(
    ["📋 Danh sách", "➕ Thêm / Sửa / Xóa", "📊 Thống kê", "🏆 Top-k", "📁 CSV"])

# ---------------- Tab danh sách ----------------
with tab_ds:
    c1, c2, c3 = st.columns([2, 1, 1])
    che_do = c1.radio("Tìm theo", ["Tên (Trie, không cần dấu)", "Mã KH (dict)"], horizontal=True)
    tu_khoa = c1.text_input("Từ khóa", placeholder="vd: tran thi  hoặc  KH000001")
    loai = c2.selectbox("Loại KH", ["Tất cả"] + LOAI_HOP_LE)
    dp = c3.selectbox("Địa phương", ["Tất cả"] + DIA_PHUONG)
    s1, s2 = st.columns(2)
    sx = s1.selectbox("Sắp xếp theo", ["ho_ten", "so_du", "ngay_dk", "ma_kh"],
                      format_func=lambda x: CODE_COT[x])
    giam = s2.checkbox("Giảm dần")

    if not tu_khoa:
        ds = ql.ds
    elif che_do.startswith("Tên"):
        ds = ql.tim_theo_ten(tu_khoa)
    else:
        kh = ql.tra_cuu(tu_khoa.strip().upper())
        ds = [kh] if kh else []
    if loai != "Tất cả":
        ds = [k for k in ds if k["loai_kh"] == loai]
    if dp != "Tất cả":
        ds = [k for k in ds if k["dia_phuong"] == dp]
    ds = ql.sap_xep(sx, giam, ds)          # Merge Sort

    st.caption(f"Hiển thị {len(ds)} / {len(ql)} khách hàng")
    st.dataframe(bang(ds), width="stretch", height=420, hide_index=True,
                 column_config={"Số dư (VND)": st.column_config.NumberColumn(format="%,.0f")})

# ---------------- Tab thêm / sửa / xóa ----------------
with tab_them:
    st.subheader("Thêm khách hàng")
    with st.form("form_them", clear_on_submit=False):
        a, b = st.columns(2)
        ma = a.text_input("Mã KH", value=f"KH{len(ql) + 1001:06d}")
        ten = b.text_input("Họ tên")
        cccd = a.text_input("CCCD (12 số)")
        sdt = b.text_input("SĐT (10 số, bắt đầu 0)")
        email = a.text_input("Email")
        dia = b.selectbox("Địa phương", DIA_PHUONG)
        lk = a.selectbox("Loại KH", LOAI_HOP_LE)
        sd = b.number_input("Số dư (VND)", min_value=0.0, step=100000.0)
        nd = a.date_input("Ngày đăng ký", value=date.today())
        if st.form_submit_button("Thêm", type="primary"):
            bao(ql.them({"ma_kh": ma, "ho_ten": ten, "cccd": cccd, "sdt": sdt, "email": email,
                         "dia_phuong": dia, "loai_kh": lk, "so_du": sd, "ngay_dk": nd}))

    st.divider()
    st.subheader("Sửa / Xóa theo mã KH")
    ma_chon = st.text_input("Nhập mã KH cần thao tác", placeholder="KH000001").strip().upper()
    kh = ql.tra_cuu(ma_chon) if ma_chon else None
    if ma_chon and not kh:
        st.warning("Không tìm thấy mã này")
    if kh:
        with st.form("form_sua"):
            a, b = st.columns(2)
            ten2 = a.text_input("Họ tên", kh["ho_ten"])
            sdt2 = b.text_input("SĐT", kh["sdt"])
            mail2 = a.text_input("Email", kh["email"])
            sd2 = b.number_input("Số dư (VND)", min_value=0.0, value=float(kh["so_du"]), step=100000.0)
            lk2 = a.selectbox("Loại KH", LOAI_HOP_LE, index=LOAI_HOP_LE.index(kh["loai_kh"]))
            dia2 = b.selectbox("Địa phương", DIA_PHUONG,
                               index=DIA_PHUONG.index(kh["dia_phuong"]) if kh["dia_phuong"] in DIA_PHUONG else 0)
            if st.form_submit_button("Lưu thay đổi", type="primary"):
                bao(ql.sua(ma_chon, ho_ten=ten2, sdt=sdt2, email=mail2, so_du=sd2,
                           loai_kh=lk2, dia_phuong=dia2))
        xac_nhan = st.checkbox(f"Tôi chắc chắn muốn xóa {ma_chon}")
        if st.button("🗑️ Xóa khách hàng", disabled=not xac_nhan):
            bao(ql.xoa(ma_chon))
            st.rerun()

# ---------------- Tab thống kê ----------------
with tab_tk:
    tong = sum(k["so_du"] for k in ql.ds)
    m1, m2, m3 = st.columns(3)
    m1.metric("Số khách hàng", len(ql))
    m2.metric("Tổng số dư", vnd(tong) + " ₫")
    m3.metric("Số dư trung bình", vnd(tong / len(ql) if len(ql) else 0) + " ₫")

    g1, g2 = st.columns(2)
    for cot, tieu_de, khung in (("loai_kh", "Theo loại khách hàng", g1),
                                ("dia_phuong", "Theo địa phương", g2)):
        tk = ql.thong_ke(cot)
        df = pd.DataFrame({"Nhóm": list(tk),
                           "Số lượng": [v["so_luong"] for v in tk.values()],
                           "Tổng số dư": [v["tong_so_du"] for v in tk.values()]})
        with khung:
            st.subheader(tieu_de)
            st.bar_chart(df.set_index("Nhóm")["Số lượng"], color="#0b8a84")
            st.dataframe(df.sort_values("Số lượng", ascending=False), hide_index=True,
                         width="stretch",
                         column_config={"Tổng số dư": st.column_config.NumberColumn(format="%,.0f")})

# ---------------- Tab Top-k ----------------
with tab_top:
    k = st.slider("Số khách hàng (k)", 1, 50, 10)
    top = ql.top_k_so_du(k)                  # Heap
    df = bang(top)
    df.insert(0, "Hạng", range(1, len(df) + 1))
    st.dataframe(df, width="stretch", hide_index=True,
                 column_config={"Số dư (VND)": st.column_config.NumberColumn(format="%,.0f")})
    st.bar_chart(pd.DataFrame({"Số dư": [t["so_du"] for t in top]},
                              index=[t["ho_ten"] for t in top]), color="#b8893b")

# ---------------- Tab CSV ----------------
with tab_csv:
    st.subheader("Xuất CSV")
    buf = io.StringIO()
    w = csv.DictWriter(buf, fieldnames=ql.TRUONG)
    w.writeheader()
    for kh in ql.ds:
        w.writerow({**kh, "ngay_dk": str(kh["ngay_dk"])})
    st.download_button("⬇️ Tải khach_hang.csv", buf.getvalue().encode("utf-8-sig"),
                       "khach_hang.csv", "text/csv")
    st.subheader("Nhập CSV")
    f = st.file_uploader("Chọn file CSV (cùng định dạng file xuất)", type="csv")
    if f is not None and st.button("Nhập dữ liệu"):
        tam = "_tam_nhap.csv"
        with open(tam, "wb") as out:
            out.write(f.getvalue())
        so_them, loi = ql.doc_csv(tam)
        st.success(f"Đã thêm {so_them} khách hàng, {len(loi)} dòng lỗi")
        if loi:
            st.dataframe(pd.DataFrame(loi, columns=["Dòng", "Lý do"]), hide_index=True)
