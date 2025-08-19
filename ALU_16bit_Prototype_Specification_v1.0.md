# 16-bit ALU 原型驗證版規格書
## Arithmetic Logic Unit Prototype Specification v1.0

---

## 執行摘要

本文件定義了一個16位元算術邏輯單元(ALU)的原型驗證版規格，適用於嵌入式處理器和微控制器應用。該ALU採用RISC架構設計理念，提供高效的算術和邏輯運算能力，目標應用包括IoT裝置、工業控制系統和嵌入式運算平台。

### 關鍵特性
- **資料寬度**: 16-bit
- **架構類型**: RISC (精簡指令集)
- **目標頻率**: 100-200 MHz
- **製程技術**: 65nm CMOS
- **功耗目標**: < 50mW @ 100MHz
- **面積估算**: ~0.15 mm²

---

## 1. 產品概述

### 1.1 功能描述
16-bit ALU是處理器核心的關鍵運算單元，負責執行所有算術和邏輯運算。本設計優化了功耗和面積，同時保持足夠的運算能力以滿足嵌入式應用需求。

### 1.2 主要特點
- 支援16種基本運算操作
- 單週期執行所有運算
- 完整的狀態旗標輸出
- 低功耗設計
- 可擴展架構

### 1.3 目標應用
- 嵌入式微控制器
- IoT感測器節點
- 工業控制器
- 智慧家電控制
- 電池供電裝置

---

## 2. 功能方塊圖

```
                    ┌─────────────────────────────────┐
                    │          16-bit ALU             │
                    │                                 │
    A[15:0] ───────►│  ┌──────────┐                  │
                    │  │          │                  │
    B[15:0] ───────►│  │  運算    │                  │
                    │  │  核心    │───► Result[15:0] │
    OpCode[3:0] ───►│  │          │                  │
                    │  └──────────┘                  │
    Cin ───────────►│                                │
                    │  ┌──────────┐                  │
                    │  │  狀態    │───► Zero         │
                    │  │  旗標    │───► Carry        │
                    │  │  產生器  │───► Overflow     │
                    │  └──────────┘───► Negative     │
                    │                                 │
                    └─────────────────────────────────┘
```

---

## 3. 指令集定義

### 3.1 操作碼對應表

| OpCode | 助記符 | 運算描述 | 運算公式 | 影響旗標 |
|--------|--------|----------|----------|----------|
| 0000 | ADD | 加法 | Result = A + B + Cin | Z,C,V,N |
| 0001 | SUB | 減法 | Result = A - B - Cin | Z,C,V,N |
| 0010 | AND | 邏輯AND | Result = A & B | Z,N |
| 0011 | OR | 邏輯OR | Result = A \| B | Z,N |
| 0100 | XOR | 邏輯XOR | Result = A ^ B | Z,N |
| 0101 | NOT | 邏輯NOT | Result = ~A | Z,N |
| 0110 | LSL | 邏輯左移 | Result = A << 1 | Z,C,N |
| 0111 | LSR | 邏輯右移 | Result = A >> 1 | Z,C,N |
| 1000 | ASR | 算術右移 | Result = A >>> 1 | Z,C,N |
| 1001 | ROL | 循環左移 | Result = ROL(A) | Z,C,N |
| 1010 | ROR | 循環右移 | Result = ROR(A) | Z,C,N |
| 1011 | INC | 遞增 | Result = A + 1 | Z,C,V,N |
| 1100 | DEC | 遞減 | Result = A - 1 | Z,C,V,N |
| 1101 | CMP | 比較 | A - B (只設定旗標) | Z,C,V,N |
| 1110 | TEST | 測試 | A & B (只設定旗標) | Z,N |
| 1111 | PASS | 直通 | Result = A | Z,N |

---

## 4. 介面信號定義

### 4.1 輸入信號

| 信號名稱 | 位元寬度 | 類型 | 描述 |
|----------|----------|------|------|
| A[15:0] | 16 | Input | 運算元A |
| B[15:0] | 16 | Input | 運算元B |
| OpCode[3:0] | 4 | Input | 操作碼 |
| Cin | 1 | Input | 進位輸入 |
| CLK | 1 | Input | 時脈信號 |
| RST_n | 1 | Input | 異步重置(低電位有效) |
| EN | 1 | Input | 使能信號 |

### 4.2 輸出信號

| 信號名稱 | 位元寬度 | 類型 | 描述 |
|----------|----------|------|------|
| Result[15:0] | 16 | Output | 運算結果 |
| Zero | 1 | Output | 零旗標 (Result == 0) |
| Carry | 1 | Output | 進位/借位旗標 |
| Overflow | 1 | Output | 溢位旗標 |
| Negative | 1 | Output | 負數旗標 (Result[15]) |

---

## 5. 時序規格

### 5.1 時序參數表 (@100MHz, 65nm, TT, 1.2V, 25°C)

| 參數 | 符號 | 最小值 | 典型值 | 最大值 | 單位 |
|------|------|--------|--------|--------|------|
| 時脈週期 | tCLK | 10 | - | - | ns |
| 設置時間 | tSU | 1.5 | - | - | ns |
| 保持時間 | tH | 0.5 | - | - | ns |
| 傳播延遲 | tPD | - | 3.5 | 5.0 | ns |
| 輸出延遲 | tCO | - | 2.0 | 3.0 | ns |

### 5.2 時序波形圖

```
        ┌─┐   ┌─┐   ┌─┐   ┌─┐
CLK  ───┘ └───┘ └───┘ └───┘ └───
        
        ╱─────╲─────╱─────╲─────
A,B    ╱ Valid Data ╲ Next Data ╲
       ╲─────╱─────╲─────╱─────
       
              ╱─────────╲─────────
Result       ╱  Valid   ╲  Next
             ╲─────────╱─────────
       |←tSU→|←──tCO──→|
```

---

## 6. 電氣特性

### 6.1 絕對最大額定值

| 參數 | 符號 | 最小值 | 最大值 | 單位 |
|------|------|--------|--------|------|
| 電源電壓 | VDD | -0.5 | 1.5 | V |
| 輸入電壓 | VIN | -0.5 | VDD+0.5 | V |
| 工作溫度 | TOP | -40 | 125 | °C |
| 儲存溫度 | TSTG | -65 | 150 | °C |

### 6.2 推薦工作條件

| 參數 | 符號 | 最小值 | 典型值 | 最大值 | 單位 |
|------|------|--------|--------|--------|------|
| 電源電壓 | VDD | 1.08 | 1.2 | 1.32 | V |
| 工作溫度 | TOP | -25 | 25 | 85 | °C |
| 時脈頻率 | fCLK | 1 | 100 | 200 | MHz |

### 6.3 功耗特性

| 條件 | 動態功耗 | 靜態功耗 | 總功耗 | 單位 |
|------|----------|----------|--------|------|
| 100MHz, 1.2V, 25°C | 45 | 5 | 50 | mW |
| 200MHz, 1.2V, 25°C | 90 | 5 | 95 | mW |
| 待機模式 | 0 | 5 | 5 | mW |

---

## 7. 驗證測試計劃

### 7.1 功能驗證測試

#### 7.1.1 基本運算測試
```
測試向量範例 (ADD運算):
A = 0x1234, B = 0x5678, Cin = 0
預期結果: Result = 0x68AC, C = 0, Z = 0, V = 0, N = 0

A = 0xFFFF, B = 0x0001, Cin = 0  
預期結果: Result = 0x0000, C = 1, Z = 1, V = 0, N = 0
```

#### 7.1.2 邊界條件測試
- 最大正數相加 (0x7FFF + 0x7FFF)
- 最小負數相減 (0x8000 - 0x0001)
- 零值運算
- 溢位檢測

### 7.2 時序驗證測試
- 設置/保持時間違規檢查
- 關鍵路徑延遲測量
- 多頻率操作測試

### 7.3 覆蓋率目標
- 程式碼覆蓋率: > 95%
- 功能覆蓋率: 100%
- 狀態機覆蓋率: 100%

---

## 8. 應用電路範例

### 8.1 典型連接圖

```verilog
// Verilog實例化範例
ALU_16bit u_alu (
    .CLK      (sys_clk),
    .RST_n    (sys_rst_n),
    .EN       (alu_enable),
    .A        (reg_a),
    .B        (reg_b),
    .OpCode   (instruction[3:0]),
    .Cin      (carry_in),
    .Result   (alu_result),
    .Zero     (flag_z),
    .Carry    (flag_c),
    .Overflow (flag_v),
    .Negative (flag_n)
);
```

### 8.2 暫存器檔案整合

```
┌────────────┐      ┌─────────┐      ┌────────────┐
│  Register  │─────►│   ALU   │─────►│  Register  │
│   File A   │      │  16-bit │      │   File B   │
└────────────┘      └─────────┘      └────────────┘
                          ▲
                          │
                    ┌─────────┐
                    │ Control │
                    │  Unit   │
                    └─────────┘
```

---

## 9. 設計約束和實現指南

### 9.1 合成約束
```tcl
# Synopsys Design Compiler約束範例
set_operating_conditions -min BCCOM -max WCCOM
create_clock -name CLK -period 10 [get_ports CLK]
set_input_delay -clock CLK -max 2.0 [all_inputs]
set_output_delay -clock CLK -max 2.0 [all_outputs]
set_max_area 0.15
```

### 9.2 設計建議
1. 使用並行前綴加法器優化ADD/SUB路徑
2. 實現早期零檢測邏輯
3. 採用時脈閘控技術降低功耗
4. 關鍵路徑應小於5ns

---

## 10. 版本歷史

| 版本 | 日期 | 作者 | 變更描述 |
|------|------|------|----------|
| 1.0 | 2024-01-19 | 系統 | 初始原型驗證版 |

---

## 附錄 A: 縮寫表

| 縮寫 | 全稱 | 中文說明 |
|------|------|----------|
| ALU | Arithmetic Logic Unit | 算術邏輯單元 |
| RISC | Reduced Instruction Set Computer | 精簡指令集電腦 |
| LSB | Least Significant Bit | 最低有效位元 |
| MSB | Most Significant Bit | 最高有效位元 |
| TT | Typical-Typical | 典型製程角 |
| FF | Fast-Fast | 快速製程角 |
| SS | Slow-Slow | 慢速製程角 |

---

## 附錄 B: 參考文獻

1. Patterson, D. A., & Hennessy, J. L. (2017). Computer Organization and Design RISC-V Edition
2. Weste, N., & Harris, D. (2015). CMOS VLSI Design: A Circuits and Systems Perspective
3. IEEE Std 1364-2005 - IEEE Standard for Verilog Hardware Description Language

---

**文件結束**

*本規格書為原型驗證版本，最終產品規格可能會有所調整*