// SPDX-License-Identifier: GPL-2.0
// Copyright (C) 2022 Samuel Demeulemeester
//

#include "stdint.h"
#include "string.h"
#include "display.h"

#include "boot.h"
#include "bootparams.h"
#include "config.h"
#include "efi.h"
#include "memctrl.h"
#include "pmem.h"
#include "vmem.h"
#include "smbios.h"

#define LINE_DMI 23

static const uint8_t *table_start = NULL;
static uint32_t table_length = 0; // 16-bit in SMBIOS v2, 32-bit in SMBIOS v3.

static const efi_guid_t SMBIOS2_GUID = { 0xeb9d2d31, 0x2d88, 0x11d3, {0x9a, 0x16, 0x00, 0x90, 0x27, 0x3f, 0xc1, 0x4d} };

// SMBIOS v3 compliant FW must include an SMBIOS v2 table, but maybe parse SM3 table later...
// static const efi_guid_t SMBIOS3_GUID = { 0xf2fd1544, 0x9794, 0x4a2c, {0x99, 0x2e, 0xe5, 0xbb, 0xcf, 0x20, 0xe3, 0x94} };

struct system_info *dmi_system_info;
struct baseboard_info *dmi_baseboard_info;
static struct mem_dev default_memory_device;
struct mem_dev *dmi_memory_device = &default_memory_device;

dimm_info_t dimms[MAX_DIMMS];
int dimm_count = 0;
static bool slot_ecc_event_seen = false;
static uint8_t slot_ecc_last_channel = 0;
static uint16_t slot_ecc_last_core = 0;
static uint64_t slot_ecc_last_addr = 0;
static uint32_t slot_ecc_last_count = 0;

typedef struct {
    uint16_t handle;
    uint64_t size_bytes;
} dimm_parse_info_t;

struct mem_dev_map_addr {
    struct tstruct_header header;
    uint32_t start_addr;
    uint32_t end_addr;
    uint16_t mem_dev_handle;
    uint16_t mem_array_mapped_addr_handle;
    uint8_t partition_row_position;
    uint8_t interleave_position;
    uint8_t interleaved_data_depth;
    uint64_t ext_start_addr;
    uint64_t ext_end_addr;
} __attribute__((packed));

static char *get_tstruct_string(struct tstruct_header *header, uint16_t maxlen, int n)
{
    if (n < 1)
        return NULL;
    char *a = (char *) header + header->length;
    n--;
    do {
        if (! *a)
            n--;
        if (!n && *a)
            return a;
        a++;
    } while (a < ((char *) header + maxlen) && !( *a == 0 && *(a - 1) == 0));
    return NULL;
}

static void copy_slot_locator(char dest[32], const char *src, int slot_idx)
{
    if (src != NULL && *src != '\0') {
        int i = 0;
        while (i < 31 && src[i] != '\0') {
            dest[i] = src[i];
            i++;
        }
        dest[i] = '\0';
        return;
    }

    dest[0] = 'D';
    dest[1] = 'I';
    dest[2] = 'M';
    dest[3] = 'M';
    dest[4] = '_';
    dest[5] = '0' + ((slot_idx + 1) % 10);
    dest[6] = '\0';
}

static uint64_t get_mem_dev_size_bytes(const struct mem_dev *mem_dev, const struct tstruct_header *header)
{
    uint16_t size = mem_dev->size;

    if (size == 0 || size == 0xFFFF) {
        return 0;
    }

    if (size == 0x7FFF) {
        // SMBIOS 2.7+: Extended Size field at offset 0x1C, in MB.
        if (header->length >= 0x20) {
            const uint32_t *ext_size_ptr = (const uint32_t *)((const uint8_t *)mem_dev + 0x1C);
            return (uint64_t)(*ext_size_ptr) << 20;
        }
        return 0;
    }

    if (size & 0x8000) {
        return (uint64_t)(size & 0x7FFF) << 10;
    }

    return (uint64_t)size << 20;
}

static bool get_mem_dev_mapped_range(const struct mem_dev_map_addr *map, const struct tstruct_header *header,
                                     uint64_t *start_addr, uint64_t *end_addr)
{
    if (map->start_addr == 0xFFFFFFFF && map->end_addr == 0xFFFFFFFF) {
        if (header->length < sizeof(struct mem_dev_map_addr)) {
            return false;
        }
        if (map->ext_end_addr < map->ext_start_addr) {
            return false;
        }
        *start_addr = map->ext_start_addr;
        *end_addr = map->ext_end_addr;
        return true;
    }

    if (map->end_addr < map->start_addr) {
        return false;
    }

    *start_addr = (uint64_t)map->start_addr << 10;
    *end_addr = ((uint64_t)map->end_addr << 10) + 1023;
    return true;
}

static void estimate_dimm_ranges(dimm_parse_info_t dimm_parse_info[MAX_DIMMS])
{
    if (dimm_count == 0 || pm_map_size == 0) {
        return;
    }

    bool has_mapped_range = false;
    for (int i = 0; i < dimm_count; i++) {
        if (dimms[i].start_addr <= dimms[i].end_addr) {
            has_mapped_range = true;
            break;
        }
    }

    if (has_mapped_range) {
        return;
    }

    uint64_t phys_start = (uint64_t)pm_map[0].start << PAGE_SHIFT;
    uint64_t phys_end = (uint64_t)(pm_map[pm_map_size - 1].end << PAGE_SHIFT) - 1;
    uint64_t cursor = phys_start;

    for (int i = 0; i < dimm_count; i++) {
        if (dimm_parse_info[i].size_bytes == 0 || cursor > phys_end) {
            continue;
        }

        dimms[i].start_addr = cursor;
        uint64_t end_addr = cursor + dimm_parse_info[i].size_bytes - 1;
        dimms[i].end_addr = end_addr > phys_end ? phys_end : end_addr;
        cursor = dimms[i].end_addr + 1;
    }
}

#if (ARCH_BITS == 64)
static smbiosv2_t *find_smbiosv2_in_efi64_system_table(efi64_system_table_t *system_table)
{
    efi64_config_table_t *config_tables = (efi64_config_table_t *) map_region(system_table->config_tables, system_table->num_config_tables * sizeof(efi64_config_table_t), true);
    if (config_tables == NULL) return NULL;

    uintptr_t table_addr = 0;
    for (uint32_t i = 0; i < system_table->num_config_tables; i++) {
        if (memcmp( & config_tables[i].guid, & SMBIOS2_GUID, sizeof(efi_guid_t)) == 0) {
            table_addr = config_tables[i].table;
        }
    }
    return (smbiosv2_t *) table_addr;
}
#endif

static smbiosv2_t *find_smbiosv2_in_efi32_system_table(efi32_system_table_t *system_table)
{
    efi32_config_table_t *config_tables = (efi32_config_table_t *) map_region(system_table->config_tables, system_table->num_config_tables * sizeof(efi32_config_table_t), true);
    if (config_tables == NULL) return NULL;

    uintptr_t table_addr = 0;
    for (uint32_t i = 0; i < system_table->num_config_tables; i++) {
        if (memcmp( & config_tables[i].guid, & SMBIOS2_GUID, sizeof(efi_guid_t)) == 0) {
            table_addr = config_tables[i].table;
        }
    }
    return (smbiosv2_t *) table_addr;
}

static uintptr_t find_smbiosv2_adr(void)
{
    const boot_params_t *boot_params = (boot_params_t *) boot_params_addr;
    const efi_info_t *efi_info = & boot_params->efi_info;

    smbiosv2_t *rp = NULL;

    if (efi_info->loader_signature == EFI32_LOADER_SIGNATURE) {
        // EFI32
        if (rp == NULL && efi_info->loader_signature == EFI32_LOADER_SIGNATURE) {
            uintptr_t system_table_addr = map_region(efi_info->sys_tab, sizeof(efi32_system_table_t), true);
            system_table_addr = map_region(system_table_addr, sizeof(efi32_system_table_t), true);
            if (system_table_addr != 0) {
                rp = find_smbiosv2_in_efi32_system_table((efi32_system_table_t *) system_table_addr);
                return (uintptr_t) rp;
            }
        }
    }
#if (ARCH_BITS == 64)
    if (rp == NULL && efi_info -> loader_signature == EFI64_LOADER_SIGNATURE) {
        // EFI64
        if (rp == NULL && efi_info->loader_signature == EFI64_LOADER_SIGNATURE) {
            uintptr_t system_table_addr = (uintptr_t) efi_info->sys_tab_hi << 32 | (uintptr_t) efi_info->sys_tab;
            system_table_addr = map_region(system_table_addr, sizeof(efi64_system_table_t), true);
            if (system_table_addr != 0) {
                rp = find_smbiosv2_in_efi64_system_table((efi64_system_table_t *) system_table_addr);
                return (uintptr_t) rp;
            }
        }
    }
#endif
    if (rp == NULL) {
        // BIOS
        uint8_t *dmi, *dmi_search_start;
        dmi_search_start = (uint8_t *) 0x000F0000;

        for (dmi = dmi_search_start; dmi < dmi_search_start + 0xffff0; dmi += 16) {
            if ( *dmi == '_' && *(dmi + 1) == 'S' && *(dmi + 2) == 'M' && *(dmi + 3) == '_')
                return (uintptr_t) dmi;
        }
    }

    return 0;
}

static int parse_dmi(uint16_t numstructs)
{
    const uint8_t *dmi = table_start;
    int tstruct_count = 0;
    dimm_parse_info_t dimm_parse_info[MAX_DIMMS];

    memset(dimm_parse_info, 0, sizeof(dimm_parse_info));
    memset(dimms, 0, sizeof(dimms));
    dimm_count = 0;

    // Struct type 1 is one of the mandatory types, so we're dealing with invalid data
    // if its size is lower than that of a minimal type 1 struct (plus a couple bytes).
    if (table_length < sizeof(struct system_info)) {
        return -1;
    }

    // Parse structs
    while (dmi < table_start + table_length - 2) { // -2 for header type and length.
        const struct tstruct_header *header = (struct tstruct_header *) dmi;

        // Type 1 - System Information
        if (header->type == 1 && header->length > offsetof(struct system_info, wut)) {
            // Multiple type 1 structs are not allowed by the standard. Still, effectively pick up the last one.
            dmi_system_info = (struct system_info *) dmi;
        }
        // Type 2 - Baseboard Information
        else if (header->type == 2 && header->length > offsetof(struct baseboard_info, serialnumber)) {
            // Multiple type 2 structs are allowed by the standard. Effectively pick up the last one.
            dmi_baseboard_info = (struct baseboard_info *) dmi;
        }
        // Type 17 - Memory Device
        else if (header->type == 17 && header->length > offsetof(struct mem_dev, partnum)) {
            struct mem_dev *mem_dev = (struct mem_dev *)dmi;
            // Keep one usable memory-device record for existing DDR/SPD code paths.
            if (dmi_memory_device->type <= 2 && mem_dev->type > 2) {
                dmi_memory_device = (struct mem_dev *) dmi;
            }

            if (dimm_count < MAX_DIMMS && mem_dev->type > 2) {
                uint16_t struct_length = table_length - ((const uint8_t *)header - table_start);
                char *locator = get_tstruct_string((struct tstruct_header *)header, struct_length, mem_dev->dev_locator);
                dimm_info_t *slot = &dimms[dimm_count];
                dimm_parse_info_t *slot_parse = &dimm_parse_info[dimm_count];

                memset(slot, 0, sizeof(*slot));
                copy_slot_locator(slot->locator, locator, dimm_count);

                slot->start_addr = UINT64_MAX;
                slot->end_addr = 0;
                slot_parse->handle = header->handle;
                slot_parse->size_bytes = get_mem_dev_size_bytes(mem_dev, header);
                dimm_count++;
            }
        }
        // Type 20 - Memory Device Mapped Address.
        else if (header->type == 20 && header->length >= offsetof(struct mem_dev_map_addr, interleaved_data_depth)) {
            const struct mem_dev_map_addr *map = (const struct mem_dev_map_addr *)dmi;
            uint64_t start_addr;
            uint64_t end_addr;

            if (get_mem_dev_mapped_range(map, header, &start_addr, &end_addr)) {
                for (int i = 0; i < dimm_count; i++) {
                    if (dimm_parse_info[i].handle == map->mem_dev_handle) {
                        if (dimms[i].start_addr > dimms[i].end_addr) {
                            dimms[i].start_addr = start_addr;
                            dimms[i].end_addr = end_addr;
                        } else {
                            if (start_addr < dimms[i].start_addr) {
                                dimms[i].start_addr = start_addr;
                            }
                            if (end_addr > dimms[i].end_addr) {
                                dimms[i].end_addr = end_addr;
                            }
                        }
                        break;
                    }
                }
            }
        }

        dmi += header->length;

        if (dmi >= table_start + table_length) {
            dmi_system_info = NULL;
            dmi_baseboard_info = NULL;
            return -1;
        }

        while ((dmi < table_start + table_length - 1) && !(*dmi == 0 && *(dmi + 1) == 0)) {
            dmi++;
        }

        dmi += 2;

        if ((dmi > table_start + table_length) || (++tstruct_count > numstructs)) {
            dmi_system_info = NULL;
            dmi_baseboard_info = NULL;
            return -1;
        }
    }

    estimate_dimm_ranges(dimm_parse_info);

    for (int i = 0; i < dimm_count; i++) {
        if (dimms[i].start_addr > dimms[i].end_addr) {
            dimms[i].start_addr = 0;
            dimms[i].end_addr = 0;
        }
        dimms[i].error_count = 0;
        dimms[i].has_error = false;
    }

    return 0;
}

int smbios_init(void)
{
    uintptr_t smb_adr;
    const uint8_t *dmi_start;
    const smbiosv2_t *eps;

    // Get SMBIOS Address
    smb_adr = find_smbiosv2_adr();

    if (smb_adr == 0) {
        return -1;
    }

    dmi_start = (const uint8_t *) smb_adr;
    eps = (const smbiosv2_t *) smb_adr;

    // Verify checksum
    int8_t checksum = 0;
    const uint8_t *dmi = dmi_start;

    for (; dmi < (dmi_start + eps->length); dmi++) {
        checksum += *dmi;
    }

    if (checksum) {
        return -1;
    }

    // SMBIOS 2.3 required
    if (eps->majorversion < 2 && eps->minorversion < 3) {
        return -1;
    }

    table_start = (const uint8_t *)(uintptr_t)eps->tableaddress;
    table_length = (uint32_t)eps->tablelength;

    return parse_dmi(eps->numstructs);
}

void print_smbios_startup_info(void)
{
    // Use baseboard info (struct type 2) as primary source of information,
    // and fall back to system info (struct type 1). Indeed, while the later
    // may contain less useful information than the former, its presence is
    // mandated by the successive revisions of the SMBIOS standard.
    // NOTE: we can get away with this ugly cast because the offsets of
    // .manufacturer and .productname are the same in system_info and baseboard_info.

    struct system_info *ptr = dmi_baseboard_info != NULL ?
                              (struct system_info *)dmi_baseboard_info : dmi_system_info;

    if (ptr != NULL) {
        char *sys_man, *sys_sku;

        int sl1, sl2, dmicol;

        uint16_t struct_length = table_length - ((uint8_t *)&ptr->header - (uint8_t *)table_start);

        sys_man = get_tstruct_string(&ptr->header, struct_length, ptr->manufacturer);
        if (sys_man != NULL) {
            sl1 = strlen(sys_man);

            sys_sku = get_tstruct_string(&ptr->header, struct_length, ptr->productname);
            if (sys_sku != NULL) {
                sl2 = strlen(sys_sku);

                if (sl1 && sl2) {
                    dmicol = 40 - ((sl1 + sl2) / 2);
                    dmicol = prints(LINE_DMI, dmicol, sys_man);
                    prints(LINE_DMI, dmicol + 1, sys_sku);
                }
            }
        }
    }
}

void smbios_reset_dimm_error_counts(void)
{
    for (int i = 0; i < dimm_count; i++) {
        dimms[i].error_count = 0;
        for (int chip = 0; chip < MAX_DIMM_CHIPS; chip++) {
            dimms[i].chip_error_count[chip] = 0;
        }
        dimms[i].has_error = false;
    }
    slot_ecc_event_seen = false;
    slot_ecc_last_channel = 0;
    slot_ecc_last_core = 0;
    slot_ecc_last_addr = 0;
    slot_ecc_last_count = 0;
}

void smbios_record_memory_error(uint64_t phys_addr)
{
    for (int i = 0; i < dimm_count; i++) {
        if (dimms[i].start_addr <= dimms[i].end_addr &&
            phys_addr >= dimms[i].start_addr &&
            phys_addr <= dimms[i].end_addr) {
            dimms[i].has_error = true;
            dimms[i].error_count++;
            return;
        }
    }
}

void smbios_record_data_error(uint64_t phys_addr, uint64_t xor_mask, uint8_t data_width_bits)
{
    if (data_width_bits == 0) {
        return;
    }

    for (int i = 0; i < dimm_count; i++) {
        if (dimms[i].start_addr <= dimms[i].end_addr &&
            phys_addr >= dimms[i].start_addr &&
            phys_addr <= dimms[i].end_addr) {
            uint8_t bit_limit = data_width_bits > 64 ? 64 : data_width_bits;
            for (uint8_t bit = 0; bit < bit_limit; bit++) {
                if ((xor_mask >> bit) & 1ULL) {
                    // Heuristic mapping for x8 devices: bits [0..7] => CH0, [8..15] => CH1, ...
                    uint8_t chip = bit / 8;
                    if (chip < MAX_DIMM_CHIPS) {
                        dimms[i].chip_error_count[chip]++;
                    }
                }
            }
            return;
        }
    }
}

void smbios_record_ecc_event(uint8_t channel, uint16_t core, uint64_t phys_addr, uint32_t count)
{
    slot_ecc_event_seen = true;
    slot_ecc_last_channel = channel;
    slot_ecc_last_core = core;
    slot_ecc_last_addr = phys_addr;
    slot_ecc_last_count = count;
}

void smbios_print_slot_health_summary(void)
{
    display_pinned_message(0, 0, "=================================");
    display_pinned_message(1, 10, "SLOT HEALTH");
    display_pinned_message(2, 0, "=================================");

    if (dimm_count == 0) {
        display_pinned_message(4, 0, "No DIMM slot information available");
        return;
    }

    for (int i = 0; i < dimm_count; i++) {
        display_pinned_message(3 + i, 0, "%-10s : %s (%u errors)",
                               dimms[i].locator[0] ? dimms[i].locator : "DIMM",
                               dimms[i].has_error ? "FAIL" : "OK",
                               (uintptr_t)dimms[i].error_count);
    }

    int row = 4 + dimm_count;
    display_pinned_message(row++, 0, "---------------------------------");
    display_pinned_message(row++, 0, "ECC / CHIP STATUS");

    if (!enable_ecc_polling) {
        display_pinned_message(row++, 0, "ECC polling is disabled");
        display_pinned_message(row++, 0, "Enable boot option: eccpoll");
        return;
    }

    if (!ecc_status.ecc_enabled) {
        display_pinned_message(row++, 0, "ECC not active on this system");
        display_pinned_message(row++, 0, "Required: ECC RAM + BIOS ECC enable");
        return;
    }

    display_pinned_message(row++, 0, "ECC is active");
    if (slot_ecc_event_seen) {
        display_pinned_message(row++, 0, "Last CECC: CH#%i Core#%i Addr %0*x Cnt %u",
                               slot_ecc_last_channel,
                               slot_ecc_last_core,
                               2 * sizeof(uintptr_t),
                               (uintptr_t)slot_ecc_last_addr,
                               (uintptr_t)slot_ecc_last_count);
    } else {
        display_pinned_message(row++, 0, "No ECC events captured yet");
    }

    display_pinned_message(row++, 0, "Per-chip status unavailable");
    display_pinned_message(row++, 0, "Needs ECC syndrome-to-chip decode support");
}

void smbios_draw_live_status_panel(void)
{
    const int panel_col = 48;
    const int panel_last_col = 79;
    const int panel_top = ROW_MESSAGE_T;
    const int panel_bottom = ROW_MESSAGE_B - 1;

    clear_screen_region(panel_top, panel_col, panel_bottom, panel_last_col);

    display_pinned_message(0, panel_col, "SLOT HEALTH");
    display_pinned_message(9, panel_col, "C#? heuristic");
    if (dimm_count == 0) {
        display_pinned_message(1, panel_col, "No DIMM SMBIOS data");
    } else {
        int max_rows = panel_bottom - panel_top - 5;
        int shown = dimm_count < max_rows ? dimm_count : max_rows;
        for (int i = 0; i < shown; i++) {
            const char *status = dimms[i].has_error ? "FAIL" : "OK";
            uint8_t suspect_chip = 0;
            uint64_t suspect_score = 0;
            for (uint8_t chip = 0; chip < MAX_DIMM_CHIPS; chip++) {
                if (dimms[i].chip_error_count[chip] > suspect_score) {
                    suspect_score = dimms[i].chip_error_count[chip];
                    suspect_chip = chip;
                }
            }

            if (suspect_score > 0) {
                display_pinned_message(1 + i, panel_col, "%-8s %s %u C%u?",
                                       dimms[i].locator[0] ? dimms[i].locator : "DIMM",
                                       status,
                                       (uintptr_t)dimms[i].error_count,
                                       (uintptr_t)suspect_chip);
            } else {
                display_pinned_message(1 + i, panel_col, "%-8s %s %u",
                                       dimms[i].locator[0] ? dimms[i].locator : "DIMM",
                                       status,
                                       (uintptr_t)dimms[i].error_count);
            }
        }
    }

    int row = 10;
    display_pinned_message(row++, panel_col, "ECC/CHIP");
    if (!enable_ecc_polling) {
        display_pinned_message(row++, panel_col, "Enable: eccpoll");
        return;
    }
    if (!ecc_status.ecc_enabled) {
        display_pinned_message(row++, panel_col, "Need ECC RAM+BIOS");
        return;
    }

    if (slot_ecc_event_seen) {
        display_pinned_message(row++, panel_col, "CH%u C%u CNT%u",
                               (uintptr_t)slot_ecc_last_channel,
                               (uintptr_t)slot_ecc_last_core,
                               (uintptr_t)slot_ecc_last_count);
    } else {
        display_pinned_message(row++, panel_col, "ECC active");
    }
    display_pinned_message(row++, panel_col, "Chip decode: N/A");
}
