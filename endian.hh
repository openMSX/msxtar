#ifndef ENDIAN_HH
#define ENDIAN_HH

#include <array>
#include <bit>
#include <concepts>
#include <cstdint>
#include <cstring>

// Minimal re-implementation of the corresponding functions in openMSX.
namespace Endian {

inline constexpr bool BIG    = std::endian::native == std::endian::big;
inline constexpr bool LITTLE = std::endian::native == std::endian::little;
static_assert(BIG || LITTLE, "mixed endian not supported");

// Reverse bytes in a 16-bit number: 0x1234 becomes 0x3412
[[nodiscard]] static inline uint16_t byteswap16(uint16_t x)
{
	return uint16_t(((x & 0x00FF) << 8) | ((x & 0xFF00) >> 8));
}

// Reverse bytes in a 32-bit number: 0x12345678 becomes 0x78563412
[[nodiscard]] static inline uint32_t byteswap32(uint32_t x)
{
	return  (x << 24)               |
	       ((x <<  8) & 0x00ff0000) |
	       ((x >>  8) & 0x0000ff00) |
	        (x >> 24);
}

// Use overloading to get a (statically) polymorphic byteswap() function.
[[nodiscard]] static inline uint16_t byteswap(uint16_t x) { return byteswap16(x); }
[[nodiscard]] static inline uint32_t byteswap(uint32_t x) { return byteswap32(x); }



template<bool SWAP> static inline void write_UA(void* p, std::integral auto x)
{
	if constexpr (SWAP) x = byteswap(x);
	memcpy(p, &x, sizeof(x));
}
inline void write_UA_L16(void* p, uint16_t x)
{
	write_UA<BIG>(p, x);
}
inline void write_UA_L32(void* p, uint32_t x)
{
	write_UA<BIG>(p, x);
}

template<bool SWAP, std::integral T> [[nodiscard]] static inline T read_UA(const void* p)
{
	T x;
	memcpy(&x, p, sizeof(x));
	if constexpr (SWAP) x = byteswap(x);
	return x;
}
[[nodiscard]] inline uint16_t read_UA_L16(const void* p)
{
	return read_UA<BIG, uint16_t>(p);
}
[[nodiscard]] inline uint32_t read_UA_L32(const void* p)
{
	return read_UA<BIG, uint32_t>(p);
}


class UA_L16 {
public:
	[[nodiscard]] inline operator uint16_t() const { return read_UA_L16(x.data()); }
	inline UA_L16& operator=(uint16_t a) { write_UA_L16(x.data(), a); return *this; }
private:
	std::array<uint8_t, 2> x;
};

class UA_L32 {
public:
	[[nodiscard]] inline operator uint32_t() const { return read_UA_L32(x.data()); }
	inline UA_L32& operator=(uint32_t a) { write_UA_L32(x.data(), a); return *this; }
private:
	std::array<uint8_t, 4> x;
};

static_assert(sizeof(UA_L16)  == 2, "must have size 2");
static_assert(sizeof(UA_L32)  == 4, "must have size 4");
static_assert(alignof(UA_L16) == 1, "must have alignment 1");
static_assert(alignof(UA_L32) == 1, "must have alignment 1");

} // namespace Endian

#endif
