# Build of verify, the reference verifier of the local inequality (see README.md).
#
# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
#
#   cmake -S . -B build -DCMAKE_BUILD_TYPE=Release && cmake --build build
#   cmake -S . -B build_san -DVERIFY_SANITIZE=ON && cmake --build build_san     (for the tests)
cmake_minimum_required(VERSION 3.22)
project(verify LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

option(VERIFY_SANITIZE "Build with AddressSanitizer and UndefinedBehaviorSanitizer" OFF)

if (NOT CMAKE_BUILD_TYPE AND NOT VERIFY_SANITIZE)
    set(CMAKE_BUILD_TYPE Release)
endif()

# verify: frames of seven points (the first and third certificate of the paper);
# verify8: frames of eight points (the second certificate, for the critical line).
function(add_verifier name points)
    add_executable(${name} verify.cpp)
    target_compile_definitions(${name} PRIVATE VERIFY_POINT_COUNT=${points})
    # bounds checks of the standard library stay on in every build
    target_compile_definitions(${name} PRIVATE _GLIBCXX_ASSERTIONS)
    target_compile_options(${name} PRIVATE
        -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion -Wshadow -Wold-style-cast -Wcast-qual
        -Wnull-dereference -Werror)
    if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
        target_compile_options(${name} PRIVATE -Wuseless-cast -Wduplicated-cond -Wlogical-op)
    endif()
    if (VERIFY_SANITIZE)
        target_compile_options(${name} PRIVATE -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all)
        target_link_options(${name} PRIVATE -fsanitize=address,undefined)
    endif()
endfunction()

add_verifier(verify 7)
add_verifier(verify8 8)
