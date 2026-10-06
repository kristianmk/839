# Build of law_deep, the deeper search for a law (see the head of law_deep.cpp).
#
# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
#
#   cmake -S . -B build -DCMAKE_BUILD_TYPE=Release && cmake --build build
#   cmake -S . -B build_san -DLAW_SANITIZE=ON && cmake --build build_san     (for the tests)
cmake_minimum_required(VERSION 3.22)
project(law_deep LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

option(LAW_SANITIZE "Build with AddressSanitizer and UndefinedBehaviorSanitizer" OFF)
option(LAW_NATIVE "Optimise for the processor of this machine" ON)

if (NOT CMAKE_BUILD_TYPE AND NOT LAW_SANITIZE)
    set(CMAKE_BUILD_TYPE Release)
endif()

find_package(OpenMP REQUIRED)

add_executable(law_deep law_deep.cpp)
target_link_libraries(law_deep PRIVATE OpenMP::OpenMP_CXX)
# bounds checks of the standard library stay on in every build
target_compile_definitions(law_deep PRIVATE _GLIBCXX_ASSERTIONS)
target_compile_options(law_deep PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion -Wshadow -Wold-style-cast -Wcast-qual
    -Wdouble-promotion -Wfloat-equal -Wnull-dereference -Werror)
if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    target_compile_options(law_deep PRIVATE -Wuseless-cast -Wduplicated-cond -Wlogical-op)
endif()
if (LAW_SANITIZE)
    target_compile_options(law_deep PRIVATE -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all)
    target_link_options(law_deep PRIVATE -fsanitize=address,undefined)
elseif (LAW_NATIVE)
    target_compile_options(law_deep PRIVATE -march=native)
endif()
