/* Generated automatically from machmode.def and config/riscv/riscv-modes.def
   by genmodes.  */

#ifndef GCC_INSN_MODES_H
#define GCC_INSN_MODES_H

enum machine_mode
{
  E_VOIDmode,              /* machmode.def:194 */
#define HAVE_VOIDmode
#ifdef USE_ENUM_MODES
#define VOIDmode E_VOIDmode
#else
#define VOIDmode ((void) 0, E_VOIDmode)
#endif
  E_BLKmode,               /* machmode.def:198 */
#define HAVE_BLKmode
#ifdef USE_ENUM_MODES
#define BLKmode E_BLKmode
#else
#define BLKmode ((void) 0, E_BLKmode)
#endif
  E_CCmode,                /* machmode.def:236 */
#define HAVE_CCmode
#ifdef USE_ENUM_MODES
#define CCmode E_CCmode
#else
#define CCmode ((void) 0, E_CCmode)
#endif
  E_BImode,                /* machmode.def:201 */
#define HAVE_BImode
#ifdef USE_ENUM_MODES
#define BImode E_BImode
#else
#define BImode (scalar_int_mode ((scalar_int_mode::from_int) E_BImode))
#endif
  E_QImode,                /* machmode.def:209 */
#define HAVE_QImode
#ifdef USE_ENUM_MODES
#define QImode E_QImode
#else
#define QImode (scalar_int_mode ((scalar_int_mode::from_int) E_QImode))
#endif
  E_HImode,                /* machmode.def:210 */
#define HAVE_HImode
#ifdef USE_ENUM_MODES
#define HImode E_HImode
#else
#define HImode (scalar_int_mode ((scalar_int_mode::from_int) E_HImode))
#endif
  E_SImode,                /* machmode.def:211 */
#define HAVE_SImode
#ifdef USE_ENUM_MODES
#define SImode E_SImode
#else
#define SImode (scalar_int_mode ((scalar_int_mode::from_int) E_SImode))
#endif
  E_DImode,                /* machmode.def:212 */
#define HAVE_DImode
#ifdef USE_ENUM_MODES
#define DImode E_DImode
#else
#define DImode (scalar_int_mode ((scalar_int_mode::from_int) E_DImode))
#endif
  E_TImode,                /* machmode.def:213 */
#define HAVE_TImode
#ifdef USE_ENUM_MODES
#define TImode E_TImode
#else
#define TImode (scalar_int_mode ((scalar_int_mode::from_int) E_TImode))
#endif
  E_QQmode,                /* machmode.def:239 */
#define HAVE_QQmode
#ifdef USE_ENUM_MODES
#define QQmode E_QQmode
#else
#define QQmode (scalar_mode ((scalar_mode::from_int) E_QQmode))
#endif
  E_HQmode,                /* machmode.def:240 */
#define HAVE_HQmode
#ifdef USE_ENUM_MODES
#define HQmode E_HQmode
#else
#define HQmode (scalar_mode ((scalar_mode::from_int) E_HQmode))
#endif
  E_SQmode,                /* machmode.def:241 */
#define HAVE_SQmode
#ifdef USE_ENUM_MODES
#define SQmode E_SQmode
#else
#define SQmode (scalar_mode ((scalar_mode::from_int) E_SQmode))
#endif
  E_DQmode,                /* machmode.def:242 */
#define HAVE_DQmode
#ifdef USE_ENUM_MODES
#define DQmode E_DQmode
#else
#define DQmode (scalar_mode ((scalar_mode::from_int) E_DQmode))
#endif
  E_TQmode,                /* machmode.def:243 */
#define HAVE_TQmode
#ifdef USE_ENUM_MODES
#define TQmode E_TQmode
#else
#define TQmode (scalar_mode ((scalar_mode::from_int) E_TQmode))
#endif
  E_UQQmode,               /* machmode.def:245 */
#define HAVE_UQQmode
#ifdef USE_ENUM_MODES
#define UQQmode E_UQQmode
#else
#define UQQmode (scalar_mode ((scalar_mode::from_int) E_UQQmode))
#endif
  E_UHQmode,               /* machmode.def:246 */
#define HAVE_UHQmode
#ifdef USE_ENUM_MODES
#define UHQmode E_UHQmode
#else
#define UHQmode (scalar_mode ((scalar_mode::from_int) E_UHQmode))
#endif
  E_USQmode,               /* machmode.def:247 */
#define HAVE_USQmode
#ifdef USE_ENUM_MODES
#define USQmode E_USQmode
#else
#define USQmode (scalar_mode ((scalar_mode::from_int) E_USQmode))
#endif
  E_UDQmode,               /* machmode.def:248 */
#define HAVE_UDQmode
#ifdef USE_ENUM_MODES
#define UDQmode E_UDQmode
#else
#define UDQmode (scalar_mode ((scalar_mode::from_int) E_UDQmode))
#endif
  E_UTQmode,               /* machmode.def:249 */
#define HAVE_UTQmode
#ifdef USE_ENUM_MODES
#define UTQmode E_UTQmode
#else
#define UTQmode (scalar_mode ((scalar_mode::from_int) E_UTQmode))
#endif
  E_HAmode,                /* machmode.def:251 */
#define HAVE_HAmode
#ifdef USE_ENUM_MODES
#define HAmode E_HAmode
#else
#define HAmode (scalar_mode ((scalar_mode::from_int) E_HAmode))
#endif
  E_SAmode,                /* machmode.def:252 */
#define HAVE_SAmode
#ifdef USE_ENUM_MODES
#define SAmode E_SAmode
#else
#define SAmode (scalar_mode ((scalar_mode::from_int) E_SAmode))
#endif
  E_DAmode,                /* machmode.def:253 */
#define HAVE_DAmode
#ifdef USE_ENUM_MODES
#define DAmode E_DAmode
#else
#define DAmode (scalar_mode ((scalar_mode::from_int) E_DAmode))
#endif
  E_TAmode,                /* machmode.def:254 */
#define HAVE_TAmode
#ifdef USE_ENUM_MODES
#define TAmode E_TAmode
#else
#define TAmode (scalar_mode ((scalar_mode::from_int) E_TAmode))
#endif
  E_UHAmode,               /* machmode.def:256 */
#define HAVE_UHAmode
#ifdef USE_ENUM_MODES
#define UHAmode E_UHAmode
#else
#define UHAmode (scalar_mode ((scalar_mode::from_int) E_UHAmode))
#endif
  E_USAmode,               /* machmode.def:257 */
#define HAVE_USAmode
#ifdef USE_ENUM_MODES
#define USAmode E_USAmode
#else
#define USAmode (scalar_mode ((scalar_mode::from_int) E_USAmode))
#endif
  E_UDAmode,               /* machmode.def:258 */
#define HAVE_UDAmode
#ifdef USE_ENUM_MODES
#define UDAmode E_UDAmode
#else
#define UDAmode (scalar_mode ((scalar_mode::from_int) E_UDAmode))
#endif
  E_UTAmode,               /* machmode.def:259 */
#define HAVE_UTAmode
#ifdef USE_ENUM_MODES
#define UTAmode E_UTAmode
#else
#define UTAmode (scalar_mode ((scalar_mode::from_int) E_UTAmode))
#endif
  E_HFmode,                /* config/riscv/riscv-modes.def:22 */
#define HAVE_HFmode
#ifdef USE_ENUM_MODES
#define HFmode E_HFmode
#else
#define HFmode (scalar_float_mode ((scalar_float_mode::from_int) E_HFmode))
#endif
  E_SFmode,                /* machmode.def:231 */
#define HAVE_SFmode
#ifdef USE_ENUM_MODES
#define SFmode E_SFmode
#else
#define SFmode (scalar_float_mode ((scalar_float_mode::from_int) E_SFmode))
#endif
  E_DFmode,                /* machmode.def:232 */
#define HAVE_DFmode
#ifdef USE_ENUM_MODES
#define DFmode E_DFmode
#else
#define DFmode (scalar_float_mode ((scalar_float_mode::from_int) E_DFmode))
#endif
  E_TFmode,                /* config/riscv/riscv-modes.def:23 */
#define HAVE_TFmode
#ifdef USE_ENUM_MODES
#define TFmode E_TFmode
#else
#define TFmode (scalar_float_mode ((scalar_float_mode::from_int) E_TFmode))
#endif
  E_SDmode,                /* machmode.def:272 */
#define HAVE_SDmode
#ifdef USE_ENUM_MODES
#define SDmode E_SDmode
#else
#define SDmode (scalar_float_mode ((scalar_float_mode::from_int) E_SDmode))
#endif
  E_DDmode,                /* machmode.def:273 */
#define HAVE_DDmode
#ifdef USE_ENUM_MODES
#define DDmode E_DDmode
#else
#define DDmode (scalar_float_mode ((scalar_float_mode::from_int) E_DDmode))
#endif
  E_TDmode,                /* machmode.def:274 */
#define HAVE_TDmode
#ifdef USE_ENUM_MODES
#define TDmode E_TDmode
#else
#define TDmode (scalar_float_mode ((scalar_float_mode::from_int) E_TDmode))
#endif
  E_CQImode,               /* machmode.def:267 */
#define HAVE_CQImode
#ifdef USE_ENUM_MODES
#define CQImode E_CQImode
#else
#define CQImode (complex_mode ((complex_mode::from_int) E_CQImode))
#endif
  E_CHImode,               /* machmode.def:267 */
#define HAVE_CHImode
#ifdef USE_ENUM_MODES
#define CHImode E_CHImode
#else
#define CHImode (complex_mode ((complex_mode::from_int) E_CHImode))
#endif
  E_CSImode,               /* machmode.def:267 */
#define HAVE_CSImode
#ifdef USE_ENUM_MODES
#define CSImode E_CSImode
#else
#define CSImode (complex_mode ((complex_mode::from_int) E_CSImode))
#endif
  E_CDImode,               /* machmode.def:267 */
#define HAVE_CDImode
#ifdef USE_ENUM_MODES
#define CDImode E_CDImode
#else
#define CDImode (complex_mode ((complex_mode::from_int) E_CDImode))
#endif
  E_CTImode,               /* machmode.def:267 */
#define HAVE_CTImode
#ifdef USE_ENUM_MODES
#define CTImode E_CTImode
#else
#define CTImode (complex_mode ((complex_mode::from_int) E_CTImode))
#endif
  E_HCmode,                /* machmode.def:269 */
#define HAVE_HCmode
#ifdef USE_ENUM_MODES
#define HCmode E_HCmode
#else
#define HCmode (complex_mode ((complex_mode::from_int) E_HCmode))
#endif
  E_SCmode,                /* machmode.def:269 */
#define HAVE_SCmode
#ifdef USE_ENUM_MODES
#define SCmode E_SCmode
#else
#define SCmode (complex_mode ((complex_mode::from_int) E_SCmode))
#endif
  E_DCmode,                /* machmode.def:269 */
#define HAVE_DCmode
#ifdef USE_ENUM_MODES
#define DCmode E_DCmode
#else
#define DCmode (complex_mode ((complex_mode::from_int) E_DCmode))
#endif
  E_TCmode,                /* machmode.def:269 */
#define HAVE_TCmode
#ifdef USE_ENUM_MODES
#define TCmode E_TCmode
#else
#define TCmode (complex_mode ((complex_mode::from_int) E_TCmode))
#endif
  E_VNx1BImode,            /* config/riscv/riscv-modes.def:43 */
#define HAVE_VNx1BImode
#ifdef USE_ENUM_MODES
#define VNx1BImode E_VNx1BImode
#else
#define VNx1BImode ((void) 0, E_VNx1BImode)
#endif
  E_VNx2BImode,            /* config/riscv/riscv-modes.def:44 */
#define HAVE_VNx2BImode
#ifdef USE_ENUM_MODES
#define VNx2BImode E_VNx2BImode
#else
#define VNx2BImode ((void) 0, E_VNx2BImode)
#endif
  E_VNx4BImode,            /* config/riscv/riscv-modes.def:45 */
#define HAVE_VNx4BImode
#ifdef USE_ENUM_MODES
#define VNx4BImode E_VNx4BImode
#else
#define VNx4BImode ((void) 0, E_VNx4BImode)
#endif
  E_VNx8BImode,            /* config/riscv/riscv-modes.def:46 */
#define HAVE_VNx8BImode
#ifdef USE_ENUM_MODES
#define VNx8BImode E_VNx8BImode
#else
#define VNx8BImode ((void) 0, E_VNx8BImode)
#endif
  E_VNx16BImode,           /* config/riscv/riscv-modes.def:47 */
#define HAVE_VNx16BImode
#ifdef USE_ENUM_MODES
#define VNx16BImode E_VNx16BImode
#else
#define VNx16BImode ((void) 0, E_VNx16BImode)
#endif
  E_VNx32BImode,           /* config/riscv/riscv-modes.def:48 */
#define HAVE_VNx32BImode
#ifdef USE_ENUM_MODES
#define VNx32BImode E_VNx32BImode
#else
#define VNx32BImode ((void) 0, E_VNx32BImode)
#endif
  E_VNx64BImode,           /* config/riscv/riscv-modes.def:49 */
#define HAVE_VNx64BImode
#ifdef USE_ENUM_MODES
#define VNx64BImode E_VNx64BImode
#else
#define VNx64BImode ((void) 0, E_VNx64BImode)
#endif
  E_VNx1QImode,            /* config/riscv/riscv-modes.def:173 */
#define HAVE_VNx1QImode
#ifdef USE_ENUM_MODES
#define VNx1QImode E_VNx1QImode
#else
#define VNx1QImode ((void) 0, E_VNx1QImode)
#endif
  E_VNx2QImode,            /* config/riscv/riscv-modes.def:158 */
#define HAVE_VNx2QImode
#ifdef USE_ENUM_MODES
#define VNx2QImode E_VNx2QImode
#else
#define VNx2QImode ((void) 0, E_VNx2QImode)
#endif
  E_VNx1HImode,            /* config/riscv/riscv-modes.def:164 */
#define HAVE_VNx1HImode
#ifdef USE_ENUM_MODES
#define VNx1HImode E_VNx1HImode
#else
#define VNx1HImode ((void) 0, E_VNx1HImode)
#endif
  E_VNx4QImode,            /* config/riscv/riscv-modes.def:140 */
#define HAVE_VNx4QImode
#ifdef USE_ENUM_MODES
#define VNx4QImode E_VNx4QImode
#else
#define VNx4QImode ((void) 0, E_VNx4QImode)
#endif
  E_VNx2HImode,            /* config/riscv/riscv-modes.def:140 */
#define HAVE_VNx2HImode
#ifdef USE_ENUM_MODES
#define VNx2HImode E_VNx2HImode
#else
#define VNx2HImode ((void) 0, E_VNx2HImode)
#endif
  E_VNx1SImode,            /* config/riscv/riscv-modes.def:151 */
#define HAVE_VNx1SImode
#ifdef USE_ENUM_MODES
#define VNx1SImode E_VNx1SImode
#else
#define VNx1SImode ((void) 0, E_VNx1SImode)
#endif
  E_VNx8QImode,            /* config/riscv/riscv-modes.def:135 */
#define HAVE_VNx8QImode
#ifdef USE_ENUM_MODES
#define VNx8QImode E_VNx8QImode
#else
#define VNx8QImode ((void) 0, E_VNx8QImode)
#endif
  E_VNx4HImode,            /* config/riscv/riscv-modes.def:135 */
#define HAVE_VNx4HImode
#ifdef USE_ENUM_MODES
#define VNx4HImode E_VNx4HImode
#else
#define VNx4HImode ((void) 0, E_VNx4HImode)
#endif
  E_VNx2SImode,            /* config/riscv/riscv-modes.def:135 */
#define HAVE_VNx2SImode
#ifdef USE_ENUM_MODES
#define VNx2SImode E_VNx2SImode
#else
#define VNx2SImode ((void) 0, E_VNx2SImode)
#endif
  E_VNx1DImode,            /* config/riscv/riscv-modes.def:133 */
#define HAVE_VNx1DImode
#ifdef USE_ENUM_MODES
#define VNx1DImode E_VNx1DImode
#else
#define VNx1DImode ((void) 0, E_VNx1DImode)
#endif
  E_VNx16QImode,           /* config/riscv/riscv-modes.def:136 */
#define HAVE_VNx16QImode
#ifdef USE_ENUM_MODES
#define VNx16QImode E_VNx16QImode
#else
#define VNx16QImode ((void) 0, E_VNx16QImode)
#endif
  E_VNx8HImode,            /* config/riscv/riscv-modes.def:136 */
#define HAVE_VNx8HImode
#ifdef USE_ENUM_MODES
#define VNx8HImode E_VNx8HImode
#else
#define VNx8HImode ((void) 0, E_VNx8HImode)
#endif
  E_VNx4SImode,            /* config/riscv/riscv-modes.def:136 */
#define HAVE_VNx4SImode
#ifdef USE_ENUM_MODES
#define VNx4SImode E_VNx4SImode
#else
#define VNx4SImode ((void) 0, E_VNx4SImode)
#endif
  E_VNx2DImode,            /* config/riscv/riscv-modes.def:136 */
#define HAVE_VNx2DImode
#ifdef USE_ENUM_MODES
#define VNx2DImode E_VNx2DImode
#else
#define VNx2DImode ((void) 0, E_VNx2DImode)
#endif
  E_VNx32QImode,           /* config/riscv/riscv-modes.def:137 */
#define HAVE_VNx32QImode
#ifdef USE_ENUM_MODES
#define VNx32QImode E_VNx32QImode
#else
#define VNx32QImode ((void) 0, E_VNx32QImode)
#endif
  E_VNx16HImode,           /* config/riscv/riscv-modes.def:137 */
#define HAVE_VNx16HImode
#ifdef USE_ENUM_MODES
#define VNx16HImode E_VNx16HImode
#else
#define VNx16HImode ((void) 0, E_VNx16HImode)
#endif
  E_VNx8SImode,            /* config/riscv/riscv-modes.def:137 */
#define HAVE_VNx8SImode
#ifdef USE_ENUM_MODES
#define VNx8SImode E_VNx8SImode
#else
#define VNx8SImode ((void) 0, E_VNx8SImode)
#endif
  E_VNx4DImode,            /* config/riscv/riscv-modes.def:137 */
#define HAVE_VNx4DImode
#ifdef USE_ENUM_MODES
#define VNx4DImode E_VNx4DImode
#else
#define VNx4DImode ((void) 0, E_VNx4DImode)
#endif
  E_VNx2TImode,            /* config/riscv/riscv-modes.def:137 */
#define HAVE_VNx2TImode
#ifdef USE_ENUM_MODES
#define VNx2TImode E_VNx2TImode
#else
#define VNx2TImode ((void) 0, E_VNx2TImode)
#endif
  E_VNx64QImode,           /* config/riscv/riscv-modes.def:138 */
#define HAVE_VNx64QImode
#ifdef USE_ENUM_MODES
#define VNx64QImode E_VNx64QImode
#else
#define VNx64QImode ((void) 0, E_VNx64QImode)
#endif
  E_VNx32HImode,           /* config/riscv/riscv-modes.def:138 */
#define HAVE_VNx32HImode
#ifdef USE_ENUM_MODES
#define VNx32HImode E_VNx32HImode
#else
#define VNx32HImode ((void) 0, E_VNx32HImode)
#endif
  E_VNx16SImode,           /* config/riscv/riscv-modes.def:138 */
#define HAVE_VNx16SImode
#ifdef USE_ENUM_MODES
#define VNx16SImode E_VNx16SImode
#else
#define VNx16SImode ((void) 0, E_VNx16SImode)
#endif
  E_VNx8DImode,            /* config/riscv/riscv-modes.def:138 */
#define HAVE_VNx8DImode
#ifdef USE_ENUM_MODES
#define VNx8DImode E_VNx8DImode
#else
#define VNx8DImode ((void) 0, E_VNx8DImode)
#endif
  E_VNx4TImode,            /* config/riscv/riscv-modes.def:138 */
#define HAVE_VNx4TImode
#ifdef USE_ENUM_MODES
#define VNx4TImode E_VNx4TImode
#else
#define VNx4TImode ((void) 0, E_VNx4TImode)
#endif
  E_VNx1HFmode,            /* config/riscv/riscv-modes.def:165 */
#define HAVE_VNx1HFmode
#ifdef USE_ENUM_MODES
#define VNx1HFmode E_VNx1HFmode
#else
#define VNx1HFmode ((void) 0, E_VNx1HFmode)
#endif
  E_VNx2HFmode,            /* config/riscv/riscv-modes.def:141 */
#define HAVE_VNx2HFmode
#ifdef USE_ENUM_MODES
#define VNx2HFmode E_VNx2HFmode
#else
#define VNx2HFmode ((void) 0, E_VNx2HFmode)
#endif
  E_VNx1SFmode,            /* config/riscv/riscv-modes.def:152 */
#define HAVE_VNx1SFmode
#ifdef USE_ENUM_MODES
#define VNx1SFmode E_VNx1SFmode
#else
#define VNx1SFmode ((void) 0, E_VNx1SFmode)
#endif
  E_VNx4HFmode,            /* config/riscv/riscv-modes.def:135 */
#define HAVE_VNx4HFmode
#ifdef USE_ENUM_MODES
#define VNx4HFmode E_VNx4HFmode
#else
#define VNx4HFmode ((void) 0, E_VNx4HFmode)
#endif
  E_VNx2SFmode,            /* config/riscv/riscv-modes.def:135 */
#define HAVE_VNx2SFmode
#ifdef USE_ENUM_MODES
#define VNx2SFmode E_VNx2SFmode
#else
#define VNx2SFmode ((void) 0, E_VNx2SFmode)
#endif
  E_VNx1DFmode,            /* config/riscv/riscv-modes.def:134 */
#define HAVE_VNx1DFmode
#ifdef USE_ENUM_MODES
#define VNx1DFmode E_VNx1DFmode
#else
#define VNx1DFmode ((void) 0, E_VNx1DFmode)
#endif
  E_VNx8HFmode,            /* config/riscv/riscv-modes.def:136 */
#define HAVE_VNx8HFmode
#ifdef USE_ENUM_MODES
#define VNx8HFmode E_VNx8HFmode
#else
#define VNx8HFmode ((void) 0, E_VNx8HFmode)
#endif
  E_VNx4SFmode,            /* config/riscv/riscv-modes.def:136 */
#define HAVE_VNx4SFmode
#ifdef USE_ENUM_MODES
#define VNx4SFmode E_VNx4SFmode
#else
#define VNx4SFmode ((void) 0, E_VNx4SFmode)
#endif
  E_VNx2DFmode,            /* config/riscv/riscv-modes.def:136 */
#define HAVE_VNx2DFmode
#ifdef USE_ENUM_MODES
#define VNx2DFmode E_VNx2DFmode
#else
#define VNx2DFmode ((void) 0, E_VNx2DFmode)
#endif
  E_VNx16HFmode,           /* config/riscv/riscv-modes.def:137 */
#define HAVE_VNx16HFmode
#ifdef USE_ENUM_MODES
#define VNx16HFmode E_VNx16HFmode
#else
#define VNx16HFmode ((void) 0, E_VNx16HFmode)
#endif
  E_VNx8SFmode,            /* config/riscv/riscv-modes.def:137 */
#define HAVE_VNx8SFmode
#ifdef USE_ENUM_MODES
#define VNx8SFmode E_VNx8SFmode
#else
#define VNx8SFmode ((void) 0, E_VNx8SFmode)
#endif
  E_VNx4DFmode,            /* config/riscv/riscv-modes.def:137 */
#define HAVE_VNx4DFmode
#ifdef USE_ENUM_MODES
#define VNx4DFmode E_VNx4DFmode
#else
#define VNx4DFmode ((void) 0, E_VNx4DFmode)
#endif
  E_VNx2TFmode,            /* config/riscv/riscv-modes.def:137 */
#define HAVE_VNx2TFmode
#ifdef USE_ENUM_MODES
#define VNx2TFmode E_VNx2TFmode
#else
#define VNx2TFmode ((void) 0, E_VNx2TFmode)
#endif
  E_VNx32HFmode,           /* config/riscv/riscv-modes.def:138 */
#define HAVE_VNx32HFmode
#ifdef USE_ENUM_MODES
#define VNx32HFmode E_VNx32HFmode
#else
#define VNx32HFmode ((void) 0, E_VNx32HFmode)
#endif
  E_VNx16SFmode,           /* config/riscv/riscv-modes.def:138 */
#define HAVE_VNx16SFmode
#ifdef USE_ENUM_MODES
#define VNx16SFmode E_VNx16SFmode
#else
#define VNx16SFmode ((void) 0, E_VNx16SFmode)
#endif
  E_VNx8DFmode,            /* config/riscv/riscv-modes.def:138 */
#define HAVE_VNx8DFmode
#ifdef USE_ENUM_MODES
#define VNx8DFmode E_VNx8DFmode
#else
#define VNx8DFmode ((void) 0, E_VNx8DFmode)
#endif
  E_VNx4TFmode,            /* config/riscv/riscv-modes.def:138 */
#define HAVE_VNx4TFmode
#ifdef USE_ENUM_MODES
#define VNx4TFmode E_VNx4TFmode
#else
#define VNx4TFmode ((void) 0, E_VNx4TFmode)
#endif
  MAX_MACHINE_MODE,

  MIN_MODE_RANDOM = E_VOIDmode,
  MAX_MODE_RANDOM = E_BLKmode,

  MIN_MODE_CC = E_CCmode,
  MAX_MODE_CC = E_CCmode,

  MIN_MODE_BOOL = E_BImode,
  MAX_MODE_BOOL = E_BImode,

  MIN_MODE_INT = E_QImode,
  MAX_MODE_INT = E_TImode,

  MIN_MODE_PARTIAL_INT = E_VOIDmode,
  MAX_MODE_PARTIAL_INT = E_VOIDmode,

  MIN_MODE_FRACT = E_QQmode,
  MAX_MODE_FRACT = E_TQmode,

  MIN_MODE_UFRACT = E_UQQmode,
  MAX_MODE_UFRACT = E_UTQmode,

  MIN_MODE_ACCUM = E_HAmode,
  MAX_MODE_ACCUM = E_TAmode,

  MIN_MODE_UACCUM = E_UHAmode,
  MAX_MODE_UACCUM = E_UTAmode,

  MIN_MODE_FLOAT = E_HFmode,
  MAX_MODE_FLOAT = E_TFmode,

  MIN_MODE_DECIMAL_FLOAT = E_SDmode,
  MAX_MODE_DECIMAL_FLOAT = E_TDmode,

  MIN_MODE_COMPLEX_INT = E_CQImode,
  MAX_MODE_COMPLEX_INT = E_CTImode,

  MIN_MODE_COMPLEX_FLOAT = E_HCmode,
  MAX_MODE_COMPLEX_FLOAT = E_TCmode,

  MIN_MODE_VECTOR_BOOL = E_VNx1BImode,
  MAX_MODE_VECTOR_BOOL = E_VNx64BImode,

  MIN_MODE_VECTOR_INT = E_VNx1QImode,
  MAX_MODE_VECTOR_INT = E_VNx4TImode,

  MIN_MODE_VECTOR_FRACT = E_VOIDmode,
  MAX_MODE_VECTOR_FRACT = E_VOIDmode,

  MIN_MODE_VECTOR_UFRACT = E_VOIDmode,
  MAX_MODE_VECTOR_UFRACT = E_VOIDmode,

  MIN_MODE_VECTOR_ACCUM = E_VOIDmode,
  MAX_MODE_VECTOR_ACCUM = E_VOIDmode,

  MIN_MODE_VECTOR_UACCUM = E_VOIDmode,
  MAX_MODE_VECTOR_UACCUM = E_VOIDmode,

  MIN_MODE_VECTOR_FLOAT = E_VNx1HFmode,
  MAX_MODE_VECTOR_FLOAT = E_VNx4TFmode,

  MIN_MODE_OPAQUE = E_VOIDmode,
  MAX_MODE_OPAQUE = E_VOIDmode,

  NUM_MACHINE_MODES = MAX_MACHINE_MODE
};

#define NUM_MODE_RANDOM (MAX_MODE_RANDOM - MIN_MODE_RANDOM + 1)
#define NUM_MODE_CC (MAX_MODE_CC - MIN_MODE_CC + 1)
#define NUM_MODE_INT (MAX_MODE_INT - MIN_MODE_INT + 1)
#define NUM_MODE_PARTIAL_INT 0
#define NUM_MODE_FRACT (MAX_MODE_FRACT - MIN_MODE_FRACT + 1)
#define NUM_MODE_UFRACT (MAX_MODE_UFRACT - MIN_MODE_UFRACT + 1)
#define NUM_MODE_ACCUM (MAX_MODE_ACCUM - MIN_MODE_ACCUM + 1)
#define NUM_MODE_UACCUM (MAX_MODE_UACCUM - MIN_MODE_UACCUM + 1)
#define NUM_MODE_FLOAT (MAX_MODE_FLOAT - MIN_MODE_FLOAT + 1)
#define NUM_MODE_DECIMAL_FLOAT (MAX_MODE_DECIMAL_FLOAT - MIN_MODE_DECIMAL_FLOAT + 1)
#define NUM_MODE_COMPLEX_INT (MAX_MODE_COMPLEX_INT - MIN_MODE_COMPLEX_INT + 1)
#define NUM_MODE_COMPLEX_FLOAT (MAX_MODE_COMPLEX_FLOAT - MIN_MODE_COMPLEX_FLOAT + 1)
#define NUM_MODE_VECTOR_BOOL (MAX_MODE_VECTOR_BOOL - MIN_MODE_VECTOR_BOOL + 1)
#define NUM_MODE_VECTOR_INT (MAX_MODE_VECTOR_INT - MIN_MODE_VECTOR_INT + 1)
#define NUM_MODE_VECTOR_FRACT 0
#define NUM_MODE_VECTOR_UFRACT 0
#define NUM_MODE_VECTOR_ACCUM 0
#define NUM_MODE_VECTOR_UACCUM 0
#define NUM_MODE_VECTOR_FLOAT (MAX_MODE_VECTOR_FLOAT - MIN_MODE_VECTOR_FLOAT + 1)
#define NUM_MODE_OPAQUE 0

#define CONST_MODE_NUNITS
#define CONST_MODE_PRECISION
#define CONST_MODE_SIZE
#define CONST_MODE_UNIT_SIZE
#define CONST_MODE_BASE_ALIGN
#define CONST_MODE_IBIT const
#define CONST_MODE_FBIT const
#define CONST_MODE_MASK

#define BITS_PER_UNIT (8)
#define MAX_BITSIZE_MODE_ANY_INT (16*BITS_PER_UNIT)
#define MAX_BITSIZE_MODE_ANY_MODE 32768
#define NUM_INT_N_ENTS 1
#define NUM_POLY_INT_COEFFS 2

#endif /* insn-modes.h */
