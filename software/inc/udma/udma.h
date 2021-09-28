#ifndef __UDMA_H
#define __UDMA_H

#include "../../inc/properties.h"
#include "../memory_map.h"

/*
 * Global register map
 */

// The UDMA register map is made of several channels, each channel area size is defined just below

// Periph area size in log2
#define UDMA_PERIPH_AREA_SIZE_LOG2  7

// Periph area size
#define UDMA_PERIPH_AREA_SIZE       (1<<UDMA_PERIPH_AREA_SIZE_LOG2)

// Channel area size in log2
#define UDMA_CHANNEL_SIZE_LOG2      4

// Channel area size
#define UDMA_CHANNEL_SIZE           (1<<UDMA_CHANNEL_SIZE_LOG2)

#define UDMA_FIRST_CHANNEL_OFFSET   0x80



// Each channel area is itself made of 3 areas
// The offsets are given relative to the offset of the channel

// Offset for RX part
#define UDMA_CHANNEL_RX_OFFSET      0x00

// Offset for TX part
#define UDMA_CHANNEL_TX_OFFSET      0x10

// Offset for peripheral specific part
#define UDMA_CHANNEL_CUSTOM_OFFSET  0x20


// For each channel, the RX and TX part have the following registers
// The offsets are given relative to the offset of the RX or TX part

// Start address register
#define UDMA_CHANNEL_SADDR_OFFSET        0x0

// Size register
#define UDMA_CHANNEL_SIZE_OFFSET         0x4

// Configuration register
#define UDMA_CHANNEL_CFG_OFFSET          0x8

// Int configuration register
#define UDMA_CHANNEL_INTCFG_OFFSET       0xC




// The UDMA also has a global configuration are defined here

// Configuration area offset
#define UDMA_CONF_OFFSET            0x0

// Configuration area size
#define UDMA_CONF_SIZE              0x040

// This area contains the following registers

// Clock-gating control register
#define UDMA_CONF_CG_OFFSET         0x00

// Input event control register
#define UDMA_CONF_EVTIN_OFFSET      0x04







/*
 * Register bitfields
 */

// The configuration register of the RX and TX parts for each channel can be accessed using the following bits

#define UDMA_CHANNEL_CFG_SHADOW_BIT   (5)
#define UDMA_CHANNEL_CFG_CLEAR_BIT    (5)
#define UDMA_CHANNEL_CFG_EN_BIT       (4)
#define UDMA_CHANNEL_CFG_SIZE_BIT     (1)
#define UDMA_CHANNEL_CFG_CONT_BIT     (0)
#define UDMA_CHANNEL_CFG_SHADOW   (1<<UDMA_CHANNEL_CFG_SHADOW_BIT)  // Indicates if a shadow transfer is there
#define UDMA_CHANNEL_CFG_CLEAR    (1<<UDMA_CHANNEL_CFG_CLEAR_BIT)  // Stop and clear all pending transfers
#define UDMA_CHANNEL_CFG_EN       (1<<UDMA_CHANNEL_CFG_EN_BIT)  // Start a transfer
#define UDMA_CHANNEL_CFG_SIZE_8   (0<<UDMA_CHANNEL_CFG_SIZE_BIT)  // Configure for 8-bits transfer
#define UDMA_CHANNEL_CFG_SIZE_16  (1<<UDMA_CHANNEL_CFG_SIZE_BIT)  // Configure for 16-bits transfer
#define UDMA_CHANNEL_CFG_SIZE_32  (2<<UDMA_CHANNEL_CFG_SIZE_BIT)  // Configure for 32-bits transfer
#define UDMA_CHANNEL_CFG_CONT     (1<<UDMA_CHANNEL_CFG_CONT_BIT)  // Configure for continuous mode

/*
 * Macros
 */


// Returns the configuration of an input event. Several values can be ORed together to form the full configuration
#define UDMA_CONF_EVTIN_EVT(udmaId,globalId) ((globalId)<<(udmaId*8))

// Return the offset of a peripheral from its identifier
#define UDMA_PERIPH_OFFSET(id)              (((id)<<UDMA_PERIPH_AREA_SIZE_LOG2)+UDMA_FIRST_CHANNEL_OFFSET)

// Returns the identifier of a peripheral from its offset
#define UDMA_PERIPH_GET(offset)             ((offset)>>UDMA_PERIPH_AREA_SIZE_LOG2)

// Return the offset of a channel from its identifier
#define UDMA_CHANNEL_OFFSET(id)              ((id)<<UDMA_CHANNEL_SIZE_LOG2)

// Returns the identifier of a channel from its offset
#define UDMA_CHANNEL_GET(offset)             ((offset)>>UDMA_CHANNEL_SIZE_LOG2)

// Return the id of a channel from the peripheral id
#define UDMA_CHANNEL_ID(id)                 ((id)*2)

// Return the number of events per peripheral
#define UDMA_NB_PERIPH_EVENTS_LOG2         2
#define UDMA_NB_PERIPH_EVENTS              (1<<UDMA_NB_PERIPH_EVENTS_LOG2)

// Return the periph id from the channel 
#define UDMA_PERIPH_ID(id)                 ((id)/2)

// Return the event id of a channel from the peripheral id
#define UDMA_EVENT_ID(id)                 ((id)*UDMA_NB_PERIPH_EVENTS)



#define ARCHI_SOC_EVENT_UDMA_RX(periph)   ((periph)*2)
#define ARCHI_SOC_EVENT_UDMA_TX(periph)   ((periph)*2 + 1)



// Define UMDA peripheral common register base address map

#ifdef ARCHI_UDMA_HAS_SPIM

#define ARCHI_UDMA_SPIM_RX_OFFSET     0x00
#define ARCHI_UDMA_SPIM_TX_OFFSET     0x10
#define ARCHI_UDMA_SPIM_CMD_OFFSET    0x20

#define ARCHI_UDMA_SPIM_RX_EVT  0
#define ARCHI_UDMA_SPIM_TX_EVT  1
#define ARCHI_UDMA_SPIM_CMD_EVT 2
#define ARCHI_UDMA_SPIM_EOT_EVT 3

#endif

/** @name UDMA HAL
 * The following API can be used to manage the generic part of the UDMA, i.e. for global configuration and channel enqueueing. Other HALs are available for peripheral specific parts.
 * The UDMA is in charge of moving data between peripherals and L2 memory. In order to better pipeline transfers and not loose any data between 2 transfers, 2 transfers at the same time
 * can be enqueued in the UDMA. Once the first one is finished, the UDMA starts the second, while the application should enqueue another one to always have 2 pending.
 * By default, all peripherals are clock-gated and must be explicitly activated before being used.
 * The UDMA can use input events to automatically trigger other actions like enqueuing a new transfer.
 */
/**@{*/

/** Tell if a new transfer canbe enqueued to a UDMA channel.
 * 
  \param   channelOffset   Offset of the channel
  \return         1 if another transfer can be enqueued, 0 otherwise
  */
static inline int plp_udma_canEnqueue(unsigned int channelOffset);

/** Enqueue a new transfer to a UDMA channel.
 * 
  \param   channelOffset Offset of the channel
  \param   l2Addr        Address in L2 memory where the data must be accessed (either stored or loaded)
  \param   size          Size in bytes of the transfer
  \param   cfg           Configuration of the transfer. Can be UDMA_CHANNEL_CFG_SIZE_8, UDMA_CHANNEL_CFG_SIZE_16 or UDMA_CHANNEL_CFG_SIZE_32
  */
static inline void plp_udma_enqueue(unsigned channelOffset, unsigned int l2Addr, unsigned int size, unsigned int cfg);

/** Tell if a channel is busy, i.e. if it already contains at least one on-going transfer
 * 
  \param   channelOffset Offset of the channel
  \return  1 if the channel is busy, 0 otherwise
  */
static inline int plp_udma_busy(unsigned channelOffset);

/** Configures peripheral clock-gating.
 * 
  \param   value    New configuration. There is 1 bit per peripheral, 0 means the peripheral is clock-gated. The bit number corresponds to the channel ID of the peripheral.
  */
static inline void plp_udma_cg_set(unsigned int value);

/** Returns peripheral clock-gating.
 * 
  \return The current clock-gating configuration.
  */
static inline unsigned int plp_udma_cg_get();

/** Configures input events
 * 4 input events can be configured. Each input event is made of 8 bits specifying which global event this local event refers to. This can then be used in some UDMA commands to refer to the global event.
 * 
  \param value  The new configuration. Each event is encoded on 8 bits so that it can contain a global event ID between 0 and 255.
  */
static inline void plp_udma_evtin_set(unsigned int value);

/** Returns input events configuration.
 * 
  \return The current input events configuration.
  */
static inline unsigned int plp_udma_evtin_get();


/** Channel base
 * Returns the channel base from the channel identifier
  \param id The channel identifier
  \return Channel base
 */
static inline unsigned int hal_udma_channel_base(int id);

/** Channel type (TX or RX)
 * Tells if the channel is a TX channel
  \param id The channel base address
  \return 1 if it is a TX channel
 */
static inline unsigned int hal_udma_channel_isTx(unsigned int addr);






// UDMA RX/TX Channels HAL Registers Structure
struct plpUdmaRxTxCh_struct_t{
    uint32_t rx_ch_saddr;
    uint32_t rx_ch_size;
    uint32_t rx_ch_cfg;
    uint32_t rx_ch_initcfg_unused;
    uint32_t tx_ch_saddr;
    uint32_t tx_ch_size;
    uint32_t tx_ch_cfg;
    uint32_t tx_ch_initcfg_unused;
};
typedef volatile struct plpUdmaRxTxCh_struct_t plpUdmaRxTxChHandle_t;

// UDMA RX/TX Channels HAL Register Fields Structure
typedef struct {
    uint32_t saddr:16;
    uint32_t unused:16;
} plpUdmaRxTxChSaddr_t;

typedef struct {
    uint32_t size:17;
    uint32_t unused:15;
} plpUdmaRxTxChSize_t;

typedef struct {
    uint32_t continuous:1;
    uint32_t datasize:2;
    uint32_t unused0:1;
    uint32_t enable:1; // used to check also if a transfer is under going
    uint32_t clear_pending:1; // clear transfer OR check pending transfer in queue
    uint32_t unused1:26;
} plpUdmaRxTxChCfg_t;

typedef struct {
    uint32_t unused:32;
} plpUdmaRxTxChInitCfg_t;

typedef union {
    plpUdmaRxTxChSaddr_t saddr;
    plpUdmaRxTxChSize_t size;
    plpUdmaRxTxChCfg_t cfg;
    uint32_t raw;
} plpUdmaRxTxCh_u;

// UDMA RX/TX Channels HAL functions prototype
static inline void plpUdmaRxChStartAddrSet (plpUdmaRxTxChHandle_t * handle, uint32_t data);
static inline uint32_t plpUdmaRxChStartAddrGet (plpUdmaRxTxChHandle_t * handle);
static inline void plpUdmaRxChSizeSet (plpUdmaRxTxChHandle_t * handle, uint32_t data);
static inline uint32_t plpUdmaRxChSizeGet (plpUdmaRxTxChHandle_t * handle);
static inline void plpUdmaRxChCfgSet (plpUdmaRxTxChHandle_t * handle, uint32_t data);
static inline uint32_t plpUdmaRxChCfgGet (plpUdmaRxTxChHandle_t * handle);
static inline void plpUdmaTxChStartAddrSet (plpUdmaRxTxChHandle_t * handle, uint32_t data);
static inline uint32_t plpUdmaTxChStartAddrGet (plpUdmaRxTxChHandle_t * handle);
static inline void plpUdmaTxChSizeSet (plpUdmaRxTxChHandle_t * handle, uint32_t data);
static inline uint32_t plpUdmaTxChSizeGet (plpUdmaRxTxChHandle_t * handle);
static inline void plpUdmaTxChCfgSet (plpUdmaRxTxChHandle_t * handle, uint32_t data);
static inline uint32_t plpUdmaTxChCfgGet (plpUdmaRxTxChHandle_t * handle);

//!@}

/// @cond IMPLEM

// UDMA RX/TX Channels HAL functions definition
static inline void plpUdmaRxChStartAddrSet (plpUdmaRxTxChHandle_t * handle, uint32_t data) {
    handle->rx_ch_saddr = data;
};

static inline uint32_t plpUdmaRxChStartAddrGet (plpUdmaRxTxChHandle_t * handle) {
    return handle->rx_ch_saddr;
};

static inline void plpUdmaRxChSizeSet (plpUdmaRxTxChHandle_t * handle, uint32_t data) {
    handle->rx_ch_size = data;
};

static inline uint32_t plpUdmaRxChSizeGet (plpUdmaRxTxChHandle_t * handle) {
    return handle->rx_ch_size;
};

static inline void plpUdmaRxChCfgSet (plpUdmaRxTxChHandle_t * handle, uint32_t data) {
    handle->rx_ch_cfg = data;
};

static inline uint32_t plpUdmaRxChCfgGet (plpUdmaRxTxChHandle_t * handle) {
    return handle->rx_ch_cfg;
};

static inline void plpUdmaTxChStartAddrSet (plpUdmaRxTxChHandle_t * handle, uint32_t data) {
    handle->tx_ch_saddr = data;
};

static inline uint32_t plpUdmaTxChStartAddrGet (plpUdmaRxTxChHandle_t * handle) {
    return handle->tx_ch_saddr;
};

static inline void plpUdmaTxChSizeSet (plpUdmaRxTxChHandle_t * handle, uint32_t data) {
    handle->tx_ch_size = data;
};

static inline uint32_t plpUdmaTxChSizeGet (plpUdmaRxTxChHandle_t * handle) {
    return handle->tx_ch_size;
};

static inline void plpUdmaTxChCfgSet (plpUdmaRxTxChHandle_t * handle, uint32_t data) {
    handle->tx_ch_cfg = data;
};

static inline uint32_t plpUdmaTxChCfgGet (plpUdmaRxTxChHandle_t * handle) {
    return handle->tx_ch_cfg;
};




///////////////////////////////////////////////////
// TODO Obsolete : to be removed cause deprecated
static inline unsigned int hal_udma_channel_isTx(unsigned int addr)
{
  return (addr >> UDMA_CHANNEL_SIZE_LOG2) & 1;
}

static inline int plp_udma_canEnqueue(unsigned int channelBase)
{
  return !(pulp_read32(channelBase + UDMA_CHANNEL_CFG_OFFSET) & UDMA_CHANNEL_CFG_SHADOW);
}

static inline void plp_udma_enqueue(unsigned channelBase, unsigned int l2Addr, unsigned int size, unsigned int cfg)
{
  pulp_write32(channelBase + UDMA_CHANNEL_SADDR_OFFSET, l2Addr);
  barrier();
  pulp_write32(channelBase + UDMA_CHANNEL_SIZE_OFFSET, size);
  barrier();
  pulp_write32(channelBase + UDMA_CHANNEL_CFG_OFFSET, cfg | UDMA_CHANNEL_CFG_EN);
}

static inline int plp_udma_busy(unsigned channelOffset)
{
  return (pulp_read32(channelOffset + UDMA_CHANNEL_CFG_OFFSET) & UDMA_CHANNEL_CFG_EN);
}

static inline void plp_udma_cg_set(unsigned int value) {
  pulp_write32(ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_UDMA_OFFSET + UDMA_CONF_OFFSET + UDMA_CONF_CG_OFFSET, value);
}

 static inline unsigned int plp_udma_cg_get() {
  return pulp_read32(ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_UDMA_OFFSET + UDMA_CONF_OFFSET + UDMA_CONF_CG_OFFSET);
}

static inline void plp_udma_evtin_set(unsigned int value) {
  pulp_write32(ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_UDMA_OFFSET + UDMA_CONF_OFFSET + UDMA_CONF_EVTIN_OFFSET, value);
}

static inline unsigned int plp_udma_evtin_get() {
  return pulp_read32(ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_UDMA_OFFSET + UDMA_CONF_OFFSET + UDMA_CONF_EVTIN_OFFSET);
}

static inline unsigned int hal_udma_periph_base(int id) {
  return ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_UDMA_OFFSET + UDMA_PERIPH_OFFSET(id);
}

static inline unsigned int hal_udma_channel_base(int id) {
  return ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_UDMA_OFFSET + UDMA_PERIPH_OFFSET(id>>1) + UDMA_CHANNEL_OFFSET(id&1);
}



#endif //__UDMA_H