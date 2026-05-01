#!/usr/bin/env bash
###############################################################################
# pcie_hot_reset.sh — Re-enumerate an Alveo U200 after JTAG bitstream load.
#
# After Vivado hw_manager programs a new bitstream, the FPGA's PCIe hard block
# resets.  The host must:
#   1. Remove the stale device,
#   2. Wait for the FPGA to finish configuration,
#   3. Tell the upstream PCIe bridge to retrain the link,
#   4. Rescan the bus.
#
# Usage:
#   sudo ./pcie_hot_reset.sh            # uses defaults (10ee:903f)
#   sudo ./pcie_hot_reset.sh 10ee:903f  # explicit vendor:device
#
# Run this AFTER Vivado finishes programming. The script handles the rest.
###############################################################################
set -euo pipefail

VDID="${1:-10ee:903f}"

die() { echo "ERROR: $*" >&2; exit 1; }

echo "=== PCIe hot-reset for Alveo U200 (${VDID}) ==="

###########################################################################
# Step 1: Locate endpoint and its upstream bridge
###########################################################################
# lspci -D includes domain (e.g. 0000:02:00.0); strip it for setpci/lspci -s
# but keep the full path for sysfs.
EP_LINE=$(lspci -Dd "$VDID" 2>/dev/null | head -1)
EP_BDF_FULL=$(echo "$EP_LINE" | awk '{print $1}')     # 0000:02:00.0
EP_BDF=$(echo "$EP_BDF_FULL" | sed 's/^[0-9a-f]*://')  # 02:00.0
BRIDGE_BDF=""

if [[ -n "$EP_BDF" ]]; then
    echo "[1] Endpoint found at $EP_BDF_FULL"

    # The bridge is the parent directory in sysfs
    EP_SYSFS="/sys/bus/pci/devices/${EP_BDF_FULL}"
    if [[ -L "$EP_SYSFS" ]]; then
        BRIDGE_SYSFS=$(dirname "$(readlink -f "$EP_SYSFS")")
        BRIDGE_BDF=$(basename "$BRIDGE_SYSFS")
        echo "    Upstream bridge: $BRIDGE_BDF"
    fi

    # Save the bridge's full config space (256 bytes) as a defensive
    # snapshot.  In normal operation we only touch the PCIe Capability
    # registers below, but if anything else gets disturbed during
    # rescan we can restore the memory windows from this copy.
    if [[ -n "$BRIDGE_BDF" ]]; then
        BRIDGE_CFG_FILE="/tmp/bridge_${BRIDGE_BDF}_cfg.bin"
        echo "    Saving bridge config → $BRIDGE_CFG_FILE"
        cp "/sys/bus/pci/devices/${BRIDGE_BDF}/config" "$BRIDGE_CFG_FILE" 2>/dev/null || true
    fi

    # Remove the stale endpoint from the kernel
    echo "[2] Removing stale endpoint $EP_BDF_FULL ..."
    echo 1 > "/sys/bus/pci/devices/${EP_BDF_FULL}/remove"
    sleep 1
else
    echo "[1] Device $VDID not currently visible."
    echo "    Cannot auto-detect the upstream bridge without an endpoint."
    echo "    After the rescan below brings the device back, re-run this"
    echo "    script if you also need to retrain the link."
    echo "[2] (skip — device already absent)"
fi

###########################################################################
# Step 2: Wait for FPGA configuration + initial link training
###########################################################################
echo "[3] Waiting 5 s for FPGA configuration & link training ..."
sleep 5

###########################################################################
# Step 3: Retrain the PCIe link via the upstream bridge
###########################################################################
if [[ -n "$BRIDGE_BDF" ]]; then
    echo "[4] Retraining PCIe link on bridge $BRIDGE_BDF ..."

    # setpci's "CAP_EXP+offset" syntax resolves the PCIe Express Capability
    # base in the bridge's config space automatically — no manual cap-chain
    # walking required. The PCIe spec layout inside the cap is:
    #   +0x00  Capability ID / Next Pointer
    #   +0x10  Link Control register (16-bit)
    #   +0x12  Link Status  register (16-bit)

    # Quick sanity check: is there an Express capability at all?
    if setpci -s "$BRIDGE_BDF" CAP_EXP+0.b >/dev/null 2>&1; then
        # Read current Link Control
        LINK_CTL=$(setpci -s "$BRIDGE_BDF" CAP_EXP+0x10.w)
        echo "    Current Link Control: 0x${LINK_CTL}"

        # Set bit 5 = Retrain Link, write back
        NEW_LINK_CTL=$(printf "%04x" $(( 16#${LINK_CTL} | 0x0020 )))
        echo "    Setting Retrain Link bit → 0x${NEW_LINK_CTL}"
        setpci -s "$BRIDGE_BDF" CAP_EXP+0x10.w=${NEW_LINK_CTL}

        # Poll Link Status (bit 11 = Link Training, clears when done)
        echo "    Waiting for link training ..."
        for i in $(seq 1 20); do
            sleep 0.5
            LINK_STS=$(setpci -s "$BRIDGE_BDF" CAP_EXP+0x12.w)
            LINK_TRAINING=$(( 16#${LINK_STS} & 0x0800 ))
            if [[ $LINK_TRAINING -eq 0 ]]; then
                LINK_SPEED=$(( 16#${LINK_STS} & 0x000F ))
                LINK_WIDTH=$(( (16#${LINK_STS} >> 4) & 0x003F ))
                echo "    Link trained! Speed: Gen${LINK_SPEED}, Width: x${LINK_WIDTH}"
                break
            fi
            if [[ $i -eq 20 ]]; then
                echo "    WARNING: Link training did not complete in 10 s!"
            fi
        done
    else
        echo "    WARNING: Bridge $BRIDGE_BDF has no PCIe Express capability."
        echo "    Falling back to Secondary Bus Reset ..."
        setpci -s "$BRIDGE_BDF" BRIDGE_CONTROL.w=0040:0040
        sleep 1
        setpci -s "$BRIDGE_BDF" BRIDGE_CONTROL.w=0000:0040
        sleep 3
    fi

    # Restore the bridge's memory windows from the snapshot we saved
    # earlier. With the link-retrain step above using only CAP_EXP-relative
    # writes this is just defence-in-depth, but it's cheap insurance against
    # anything else (BIOS/SMM, kernel quirks) disturbing the windows during
    # rescan.
    if [[ -f "${BRIDGE_CFG_FILE:-}" ]]; then
        echo "    Restoring bridge memory windows from $BRIDGE_CFG_FILE ..."
        # Bytes 0x20-0x2F: memory base/limit + prefetch base/limit
        dd if="$BRIDGE_CFG_FILE" of="/sys/bus/pci/devices/${BRIDGE_BDF}/config" \
           bs=1 skip=32 seek=32 count=16 conv=notrunc 2>/dev/null || true
    fi
else
    echo "[4] (skip — no bridge BDF known)"
fi

###########################################################################
# Step 4: Rescan the PCI bus
###########################################################################
echo "[5] Rescanning PCI bus ..."
echo 1 > /sys/bus/pci/rescan
sleep 2

###########################################################################
# Step 5: Verify and enable - if needed
###########################################################################
echo ""
echo "=== Verification ==="

NEW_BDF_FULL=$(lspci -Dd "$VDID" 2>/dev/null | head -1 | awk '{print $1}')
NEW_BDF=$(echo "$NEW_BDF_FULL" | sed 's/^[0-9a-f]*://')

if [[ -z "$NEW_BDF" ]]; then
    echo "FAIL: Device $VDID not found after rescan."
    echo ""
    echo "Troubleshooting:"
    echo "  dmesg | tail -40"
    echo "  lspci -tv    # check if bridge still exists"
    echo ""
    echo "If the bridge itself vanished, you need a cold reboot."
    exit 1
fi

echo "Device found at $NEW_BDF_FULL"

# Check if memory space is enabled
CMD=$(setpci -s "$NEW_BDF" COMMAND.w)
MEM_EN=$(( 16#${CMD} & 0x0002 ))
BM_EN=$((  16#${CMD} & 0x0004 ))

if [[ $MEM_EN -eq 0 ]] || [[ $BM_EN -eq 0 ]]; then
    echo "Enabling Memory Space + Bus Master on $NEW_BDF ..."
    setpci -s "$NEW_BDF" COMMAND.w=0006:0006
    sleep 0.5
fi

# Show BAR info
echo ""
lspci -vvs "$NEW_BDF" 2>/dev/null | grep -E "Region|LnkSta:|Memory" || true
echo ""

# Check for [disabled] or [virtual]
BAR_LINE=$(lspci -vvs "$NEW_BDF" 2>/dev/null | grep "Region 0:" || true)
if echo "$BAR_LINE" | grep -qE '\[disabled\]|\[virtual\]'; then
    echo "WARNING: BAR0 is disabled/virtual. The bridge memory window may not cover it."
    echo ""
    echo "Bridge memory windows:"
    lspci -vvs "${BRIDGE_BDF:-unknown}" 2>/dev/null | grep -E "Memory behind|Prefetchable" || true
    echo ""
    echo "This usually means the bridge windows (set at cold boot) don't include"
    echo "the address Linux wants to assign to the BAR. Solutions:"
    echo "  1. Add 'pci=realloc' to kernel cmdline and reboot once"
    echo "  2. Cold reboot with the MCS programmed into SPI flash"
    exit 1
else
    echo "BAR0 appears OK."
fi

# Quick read test
RESOURCE="/sys/bus/pci/devices/${NEW_BDF_FULL}/resource0"
if [[ -e "$RESOURCE" ]]; then
    echo ""
    echo "resource0: $(ls -la "$RESOURCE" 2>/dev/null)"
    echo ""
    echo "Ready to load:"
    echo "  sudo ./pcie_load $RESOURCE 0x0 boot.bin"
fi

echo ""
echo "=== Done ==="
