#pragma once
// =============================================================================
// `crates/obend-fpga-hal/include/verilator_daemon_bridge.hpp`
// C++17 POSIX 4 MiB Shared-Memory (`shm_open` + `mmap`) & Unix Domain Socket
// Bridge for Verilator 5.x Co-Simulation (`obend-silicon-sim`)
// =============================================================================

#include <cstdint>
#include <cstring>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <unistd.h>

namespace obend::fpga {

static constexpr uint64_t OBEND_MAGIC_F20    = 0x303246444E45424FULL; // "OBENDF20"
static constexpr uint64_t OBCAM_WIRE_MAGIC   = 0x31564D4143424F00ULL; // "\0OBCAMV1"
static constexpr size_t   SHM_APERTURE_BYTES = 4ULL * 1024ULL * 1024ULL; // 4 MiB

// BAR0 CSR Offsets (`0x0000..0x04FF`)
static constexpr size_t CSR_OBEND_MAGIC      = 0x0000;
static constexpr size_t CSR_OBEND_VER_CAPS   = 0x0008;
static constexpr size_t CSR_OBEND_CTRL       = 0x0010;
static constexpr size_t CSR_OBEND_CYCLES     = 0x0018;
static constexpr size_t CSR_DMA_TX_RING      = 0x0020;
static constexpr size_t CSR_DMA_RX_RING      = 0x0028;
static constexpr size_t CSR_DPR_GUARD_PIN    = 0x0030;
static constexpr size_t CSR_IN_PORT_BASE     = 0x0100; // 32 x u64 (0x0100..0x01FF)
static constexpr size_t CSR_OUT_PORT_BASE    = 0x0200; // 32 x u64 (0x0200..0x02FF)
static constexpr size_t CSR_STATE_SNAP_BASE  = 0x0300; // 32 x u64 (0x0300..0x03FF)
static constexpr size_t CSR_SILICON_CTRL     = 0x0400;
static constexpr size_t CSR_TARGET_EXPR_H    = 0x0404;
static constexpr size_t CSR_TARGET_TYPE_H    = 0x0408;
static constexpr size_t CSR_TARGET_DECL_SYM  = 0x040C;
static constexpr size_t CSR_FUEL_BUDGET      = 0x0410;
static constexpr size_t CSR_RESULT_STATUS    = 0x0414;
static constexpr size_t CSR_PERF_CYCLES      = 0x0418;
static constexpr size_t CSR_PERF_CAM_HITS    = 0x041C;
static constexpr size_t CSR_PERF_CAM_ALLOCS  = 0x0420;
static constexpr size_t CSR_PERF_BYPASS_CNT  = 0x0424;
static constexpr size_t CSR_PERF_NOC_FLITS   = 0x0428;
static constexpr size_t CSR_PERF_LUT_HITS    = 0x042C;
static constexpr size_t CSR_ZONE3_MATCH_THM  = 0x0430;

// 512-bit (64-byte) AXI4-Stream DMA Beat
struct alignas(64) AxiStream512Beat {
  uint8_t  tdata[64];
  uint64_t tkeep;
  uint8_t  tlast;
  uint8_t  _pad[55];
};

class VerilatorShmBridge {
public:
  VerilatorShmBridge() : fd_(-1), base_(nullptr) {}
  ~VerilatorShmBridge() { close(); }

  bool open_or_create(const char* shm_name) {
    fd_ = ::shm_open(shm_name, O_CREAT | O_RDWR, 0600);
    if (fd_ < 0) return false;
    if (::ftruncate(fd_, static_cast<off_t>(SHM_APERTURE_BYTES)) != 0) {
      ::close(fd_);
      fd_ = -1;
      return false;
    }
    void* ptr = ::mmap(nullptr, SHM_APERTURE_BYTES, PROT_READ | PROT_WRITE, MAP_SHARED, fd_, 0);
    if (ptr == MAP_FAILED) {
      ::close(fd_);
      fd_ = -1;
      return false;
    }
    base_ = static_cast<uint8_t*>(ptr);
    write_u64(CSR_OBEND_MAGIC, OBEND_MAGIC_F20);
    write_u64(CSR_OBEND_VER_CAPS, 0x0001000400200200ULL);
    return true;
  }

  void close() {
    if (base_) {
      ::munmap(base_, SHM_APERTURE_BYTES);
      base_ = nullptr;
    }
    if (fd_ >= 0) {
      ::close(fd_);
      fd_ = -1;
    }
  }

  uint32_t read_u32(size_t offset) const {
    uint32_t v = 0;
    std::memcpy(&v, base_ + offset, sizeof(uint32_t));
    return v;
  }

  void write_u32(size_t offset, uint32_t v) {
    std::memcpy(base_ + offset, &v, sizeof(uint32_t));
  }

  uint64_t read_u64(size_t offset) const {
    uint64_t v = 0;
    std::memcpy(&v, base_ + offset, sizeof(uint64_t));
    return v;
  }

  void write_u64(size_t offset, uint64_t v) {
    std::memcpy(base_ + offset, &v, sizeof(uint64_t));
  }

private:
  int      fd_;
  uint8_t* base_;
};

} // namespace obend::fpga
