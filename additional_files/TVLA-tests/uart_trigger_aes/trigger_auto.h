// Generated register defines for trigger

#ifndef _TRIGGER_REG_DEFS_
#define _TRIGGER_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif

//start address
#define TRIGGER0_BASE_ADDR 0x41000000
// auto added parameter
#define TRIGGER_PARAM_GPIO_O 1
// Register width
#define TRIGGER_PARAM_REG_WIDTH 32
// GPIO for trigger. (common parameters)
#define TRIGGER_GPIO_O_GPIO_O_FIELD_WIDTH 32
#define TRIGGER_GPIO_O_GPIO_O_FIELDS_PER_REG 1
#define TRIGGER_GPIO_O_MULTIREG_COUNT 1
// GPIO for trigger.
#define TRIGGER_GPIO_O (TRIGGER0_BASE_ADDR + 0x0)
#define TRIGGER_GPIO_O_REG_OFFSET 0x0
//  Trigger the Keccak
#define TRIGGER_CTRL (TRIGGER0_BASE_ADDR + 0x4)
#define TRIGGER_CTRL_REG_OFFSET 0x4
#define TRIGGER_CTRL_START 0
#define TRIGGER_CTRL_STOP 1
// Contains status information about the trigger component.
#define TRIGGER_STATUS (TRIGGER0_BASE_ADDR + 0x8)
#define TRIGGER_STATUS_REG_OFFSET 0x8
#define TRIGGER_STATUS_STATUS 0

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _TRIGGER_REG_DEFS_
// End generated register defines for trigger
