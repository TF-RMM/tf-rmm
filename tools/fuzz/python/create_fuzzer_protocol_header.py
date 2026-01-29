#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

from fuzzer_protocol import *


def create_fuzzer_protocol_header(filename):
    commands = []
    structs = []
    log_macros = []
    for k, v in RMI.payload_guess:
        inst = v()
        name = inst.name.replace(" ", "_")
        cl_name = inst.__class__.__name__
        commands.append(f"#define COMMAND_{name.upper()} {k['command']}")

        fields = []
        format_strings = []
        args = []
        for field in v.fields_desc:
            field_name = field.name.replace(" ", "_").lower()
            if isinstance(field, ByteField):
                field_type = "uint8_t"
                format_str = '0x%"PRIx8"'
            elif isinstance(field, LEShortField):
                field_type = "uint16_t"
                format_str = '0x%"PRIx16"'
            elif isinstance(field, LEIntField):
                field_type = "uint32_t"
                format_str = '0x%"PRIx32"'
            elif isinstance(field, LELongField):
                field_type = "uint64_t"
                format_str = '0x%"PRIx64"'
            else:
                raise Exception(f"Invalid field type: {type(field).__name__}")

            fields.append(f"\t{field_type} {field_name};")
            format_strings.append(f"{field_name} = {format_str}")
            args.append(f"p.{field_name}")

        field_list = "\n".join(fields)
        structs.append(f"struct packet_{name.lower()} {{\n{field_list}\n}} __packed;")

        log_format = ", ".join(format_strings)
        arg_list = ", ".join(args)
        log_macros.append(
            f'#define LOG_packet_{name.lower()}_FUNC(p) \\\n'
            f'\tfprintf(stderr, "_FH: {cl_name}({log_format}),\\n", {arg_list}); fflush(stdout)')

    with open(filename, "wt") as f:
        f.write("// Generated file\n")
        f.write("#include <stdint.h>\n")
        f.write("#include <inttypes.h>\n")
        f.write("#ifndef FUZZER_PROTOCOL_H_\n")
        f.write("#define FUZZER_PROTOCOL_H_\n\n")
        f.write("\n".join(commands))
        f.write("\n\n")
        f.write("\n\n".join(structs))
        f.write("\n\n")
        f.write("\n\n".join(log_macros))
        f.write("\n\n#endif /* FUZZER_PROTOCOL_H_ */\n")


if __name__ == "__main__":
    import sys

    create_fuzzer_protocol_header(sys.argv[1])
