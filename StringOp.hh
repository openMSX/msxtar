#ifndef STRINGOP_HH
#define STRINGOP_HH

#include <string>
#include <string_view>
#include <utility>

// Minimal re-implementation of the corresponding functions in openMSX.
namespace StringOp
{
	inline void trimRight(std::string& str, const char* chars) {
		if (auto pos = str.find_last_not_of(chars); pos != std::string::npos) {
			str.erase(pos + 1);
		} else {
			str.clear();
		}
	}
	inline void trimRight(std::string& str, char chars) {
		if (auto pos = str.find_last_not_of(chars); pos != std::string::npos) {
			str.erase(pos + 1);
		} else {
			str.clear();
		}
	}
	inline void trimRight(std::string_view& str, std::string_view chars) {
		while (!str.empty() && (chars.find(str.back()) != std::string_view::npos)) {
			str.remove_suffix(1);
		}
	}
	inline void trimRight(std::string_view& str, char chars) {
		while (!str.empty() && (str.back() == chars)) {
			str.remove_suffix(1);
		}
	}

	inline void trimLeft(std::string& str, const char* chars) {
		str.erase(0, str.find_first_not_of(chars));
	}
	inline void trimLeft(std::string& str, char chars) {
		str.erase(0, str.find_first_not_of(chars));
	}
	inline void trimLeft(std::string_view& str, std::string_view chars) {
		while (!str.empty() && (chars.find(str.front()) != std::string_view::npos)) {
			str.remove_prefix(1);
		}
	}
	inline void trimLeft(std::string_view& str, char chars) {
		while (!str.empty() && (str.front() == chars)) {
			str.remove_prefix(1);
		}
	}


	[[nodiscard]] inline std::pair<std::string_view, std::string_view> splitOnFirst(std::string_view str, std::string_view chars)
	{
		if (auto pos = str.find_first_of(chars); pos == std::string_view::npos) {
			return {str, std::string_view{}};
		} else {
			return {str.substr(0, pos), str.substr(pos + 1)};
		}
	}
	[[nodiscard]] inline std::pair<std::string_view, std::string_view> splitOnFirst(std::string_view str, char chars)
	{
		if (auto pos = str.find_first_of(chars); pos == std::string_view::npos) {
			return {str, std::string_view{}};
		} else {
			return {str.substr(0, pos), str.substr(pos + 1)};
		}
	}

	[[nodiscard]] inline std::pair<std::string_view, std::string_view> splitOnLast(std::string_view str, std::string_view chars)
	{
		if (auto pos = str.find_last_of(chars); pos == std::string_view::npos) {
			return {std::string_view{}, str};
		} else {
			return {str.substr(0, pos), str.substr(pos + 1)};
		}
	}
	[[nodiscard]] inline std::pair<std::string_view, std::string_view> splitOnLast(std::string_view str, char chars)
	{
		if (auto pos = str.find_last_of(chars); pos == std::string_view::npos) {
			return {std::string_view{}, str};
		} else {
			return {str.substr(0, pos), str.substr(pos + 1)};
		}
	}
}

#endif
