#!/bin/bash
# Usage: fix_pci_json.sh <builddir>
FIX_DIR="$1"
sed "s|<fixup_path>|"$FIX_DIR"|g" $FIX_DIR/pci.json > "$FIX_DIR/pci_fixedup.json"
