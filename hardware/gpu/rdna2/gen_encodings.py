#!/usr/bin/env python3
"""Generate the Lean data modules of Obend.Hardware.Gpu.Rdna2 from AMD's machine-readable RDNA2 ISA.

    python3 -I gen_encodings.py amdgpu_isa_rdna2.xml OUT_DIR

Writes OUT_DIR/Encodings.lean (encodings, conditions, fields, operand types) and OUT_DIR/Insts.lean plus
OUT_DIR/Insts/N.lean (every instruction with every InstructionEncoding and its operands, in chunks that
each elaborate inside the tier-1 budget). The types are Obend.Hardware.Gpu.Rdna2.Spec; the schema is
isa_spec_manager/documentation/spec_documentation.md. Every value is read from the XML; the only
transformation is keeping register-name runs as runs (RegRun), verified here against the XML's list.
hardware/gpu/isa_check.sh regenerates and compares bytes.
"""
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

CHUNK = 96


def tx(e, tag):
    c = e.find(tag)
    return (c.text or "").strip() if c is not None else ""


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_list(items, chunk=64, sep=", "):
    """A list literal, split into `++`-joined pieces so that no literal exceeds Lean's recursion depth."""
    items = list(items)
    if len(items) <= chunk:
        return "[" + sep.join(items) + "]"
    return "(" + " ++ ".join("[" + sep.join(items[i:i + chunk]) + "]" for i in range(0, len(items), chunk)) + ")"


def bool_(s):
    return "true" if str(s).lower() == "true" else "false"


def cond_expr(e):
    """The XML's CondtionExpression tree as a Lean `Cond` term."""
    if e.tag == "lit":
        return f"(.lit {'true' if e.get('val') == '1' else 'false'})"
    assert e.tag == "op", e.tag
    t = e.get("type")
    kids = [k for k in e if k.tag in ("op", "lit", "id")]
    if t == "&&":
        return f"(.and {cond_expr(kids[0])} {cond_expr(kids[1])})"
    if t in ("==", "!="):
        field = field_of(kids[0])
        lit = kids[1]
        assert lit.tag == "lit"
        return f"(.{'eq' if t == '==' else 'ne'} {lean_str(field)} {int(lit.get('val'))})"
    if t in (".within", ".notwithin"):
        field = field_of(kids[0])
        arr = kids[1]
        assert arr.tag == "op" and arr.get("type") == ".cons_array"
        vals = [int(l.get("val")) for l in arr if l.tag == "lit"]
        return f"(.{'within' if t == '.within' else 'notWithin'} {lean_str(field)} [{', '.join(map(str, vals))}])"
    raise SystemExit(f"unknown condition op {t}")


def field_of(e):
    """`.fieldderef (.fieldderef INST ENC) FIELD` -> FIELD."""
    assert e.tag == "op" and e.get("type") == ".fieldderef", ET.tostring(e)
    ids = [k for k in e if k.tag == "id"]
    return ids[-1].get("val")


def bits_to_u32(s):
    """A binary identifier/mask string, MSB first (bit 0 rightmost; the first dword is bits 31..0), whose set bits must lie in the first dword."""
    v = int(s, 2)
    first, rest = v & 0xFFFFFFFF, v >> 32
    assert rest == 0, f"bits outside the first dword: {s}"
    return first


def gen_encodings(isa):
    out = []
    for enc in isa.find("Encodings"):
        name = tx(enc, "EncodingName")
        order = int(enc.get("Order"))
        bits = int(tx(enc, "BitCount"))
        mask = bits_to_u32(tx(enc, "EncodingIdentifierMask"))
        ids = [bits_to_u32(i.text.strip()) for i in enc.find("EncodingIdentifiers")]
        conds = []
        for c in enc.find("EncodingConditions"):
            ex = c.find("CondtionExpression")
            conds.append(f"⟨{lean_str(tx(c, 'ConditionName'))}, {cond_expr(ex[0])}⟩")
        fields = []
        for f in enc.find("MicrocodeFormat").find("BitMap"):
            rs = ", ".join(f"⟨{tx(r, 'BitOffset')}, {tx(r, 'BitCount')}⟩" for r in f.find("BitLayout"))
            fields.append(f"⟨{lean_str(tx(f, 'FieldName'))}, [{rs}]⟩")
        ids_s = lean_list((f"0x{i:08x}" for i in ids), chunk=32)
        out.append((name,
            f"⟨{lean_str(name)}, {order}, {bits}, 0x{mask:08x},\n    {ids_s},\n"
            f"    {lean_list(conds)},\n    {lean_list(fields)}⟩"
        ))
    return out


def gen_operand_types(isa):
    out = []
    for ot in isa.find("OperandTypes"):
        name = tx(ot, "OperandTypeName")
        part = bool_(ot.get("IsPartitioned"))
        subs = [s.text.strip() for s in ot.find("Subtypes")] if ot.find("Subtypes") is not None else []
        vals = []
        if ot.find("OperandPredefinedValues") is not None:
            vals = [(tx(v, "Name"), int(tx(v, "Value"))) for v in ot.find("OperandPredefinedValues")]
        runs, specials = [], []
        i = 0
        while i < len(vals):
            m = re.fullmatch(r"([sv])(\d+)", vals[i][0])
            if m:
                prefix, first, value = m.group(1), int(m.group(2)), vals[i][1]
                j = i
                while j < len(vals):
                    mj = re.fullmatch(r"([sv])(\d+)", vals[j][0])
                    if not (mj and mj.group(1) == prefix and int(mj.group(2)) == first + (j - i) and vals[j][1] == value + (j - i)):
                        break
                    j += 1
                runs.append((prefix, first, j - i, value))
                # verify the run reproduces the XML's names and values exactly
                for k in range(i, j):
                    assert vals[k] == (f"{prefix}{first + (k - i)}", value + (k - i))
                i = j
            else:
                specials.append(vals[i])
                i += 1
        runs_s = lean_list(f"⟨{lean_str(p)}, {f}, {c}, {v}⟩" for p, f, c, v in runs)
        sp_s = lean_list(f"({lean_str(n)}, {v})" for n, v in specials)
        out.append((name, f"⟨{lean_str(name)}, {part}, {lean_list(lean_str(s) for s in subs)}, {runs_s}, {sp_s}⟩"))
    return out


def gen_instructions(isa):
    out = []
    for ins in isa.find("Instructions"):
        name = tx(ins, "InstructionName")
        fl = {c.tag: c.text.strip() for c in ins.find("InstructionFlags")}
        encs = []
        for ie in ins.find("InstructionEncodings"):
            ops = []
            for op in ie.find("Operands"):
                ops.append(
                    f"⟨{lean_str(tx(op, 'FieldName'))}, {lean_str(tx(op, 'OperandType'))}, {lean_str(tx(op, 'DataFormatName'))}, "
                    f"{tx(op, 'OperandSize') or 0}, {bool_(op.get('Input'))}, {bool_(op.get('Output'))}, "
                    f"{bool_(op.get('IsImplicit'))}, {bool_(op.get('IsBinaryMicrocodeRequired'))}⟩"
                )
            opcode = tx(ie, "Opcode")
            radix = ie.find("Opcode").get("Radix", "10")
            opcode_v = int(opcode, int(radix))
            encs.append(f"      ⟨{lean_str(tx(ie, 'EncodingName'))}, {lean_str(tx(ie, 'EncodingCondition'))}, {opcode_v},\n        {lean_list(ops)}⟩")
        out.append(
            f"  ⟨{lean_str(name)}, {bool_(fl.get('IsBranch'))}, {bool_(fl.get('IsConditionalBranch'))}, "
            f"{bool_(fl.get('IsProgramTerminator'))}, {bool_(fl.get('IsImmediatelyExecuted'))},\n    [\n" + ",\n".join(encs) + "\n    ]⟩"
        )
    return out


HEADER = "-- Generated by hardware/gpu/rdna2/gen_encodings.py from hardware/gpu/rdna2/amdgpu_isa_rdna2.xml; do not edit\n-- (hardware/gpu/isa_check.sh regenerates and compares bytes).\nmodule\npublic import Obend.Hardware.Gpu.Rdna2.Spec\n@[expose] public section\n\nnamespace Obend.Hardware.Gpu.Rdna2\n\n"


def main():
    xml_path, out_dir = sys.argv[1], Path(sys.argv[2])
    root = ET.parse(xml_path).getroot()
    doc = root.find("Document")
    isa = root.find("ISA")
    arch = isa.find("Architecture")
    meta = (
        f"def specReleaseDate : String := {lean_str(tx(doc, 'ReleaseDate'))}\n"
        f"def specSchemaVersion : String := {lean_str(tx(doc, 'SchemaVersion'))}\n"
        f"def architectureName : String := {lean_str(tx(arch, 'ArchitectureName'))}\n"
        f"def architectureId : Nat := {tx(arch, 'ArchitectureId')}\n\n"
    )
    encs = gen_encodings(isa)
    ots = gen_operand_types(isa)
    (out_dir / "Encodings.lean").write_text(
        HEADER + meta
        + "".join(f"def enc_{n} : Encoding :=\n  {t}\n\n" for n, t in encs)
        + "/-- Every `Encoding` of the XML, in document order (`Encoding.order` is the decode order). -/\n"
        + "def encodings : List Encoding :=\n  " + lean_list((f"enc_{n}" for n, _ in encs), chunk=16, sep=",\n   ") + "\n\n"
        + "".join(f"def opr_{n} : OperandType :=\n  {t}\n\n" for n, t in ots)
        + "/-- Every `OperandType` of the XML. -/\n"
        + "def operandTypes : List OperandType :=\n  " + lean_list((f"opr_{n}" for n, _ in ots), chunk=16, sep=",\n   ") + "\n\n"
        + "end Obend.Hardware.Gpu.Rdna2\n"
    )
    insts = gen_instructions(isa)
    chunks = [insts[i:i + CHUNK] for i in range(0, len(insts), CHUNK)]
    (out_dir / "Insts").mkdir(exist_ok=True)
    for old in (out_dir / "Insts").glob("*.lean"):
        old.unlink()
    for k, ch in enumerate(chunks):
        (out_dir / "Insts" / f"C{k}.lean").write_text(
            HEADER + f"/-- Instructions {k * CHUNK} to {k * CHUNK + len(ch) - 1} of the XML, in document order. -/\n"
            + f"def instructionsChunk{k} : List Instruction := [\n" + ",\n".join(ch) + "\n]\n\n"
            + "end Obend.Hardware.Gpu.Rdna2\n"
        )
    imports = "".join(f"public import Obend.Hardware.Gpu.Rdna2.Insts.C{k}\n" for k in range(len(chunks)))
    (out_dir / "Insts.lean").write_text(
        "-- Generated by hardware/gpu/rdna2/gen_encodings.py from hardware/gpu/rdna2/amdgpu_isa_rdna2.xml; do not edit\n"
        "-- (hardware/gpu/isa_check.sh regenerates and compares bytes).\nmodule\npublic import Obend.Hardware.Gpu.Rdna2.Spec\n"
        + imports + "@[expose] public section\n\nnamespace Obend.Hardware.Gpu.Rdna2\n\n"
        + "/-- Every `Instruction` of the XML, in document order. -/\n"
        + "def instructions : List Instruction :=\n  " + " ++ ".join(f"instructionsChunk{k}" for k in range(len(chunks))) + "\n\n"
        + "end Obend.Hardware.Gpu.Rdna2\n"
    )
    print(f"{len(encs)} encodings, {len(ots)} operand types, {len(insts)} instructions in {len(chunks)} chunks -> {out_dir}")


if __name__ == "__main__":
    main()
