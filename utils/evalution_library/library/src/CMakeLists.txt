include_directories(${evaluation_library_SOURCE_DIR}/library/include)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${evaluation_library_SOURCE_DIR}/library/lib)
add_library(eval interface.cpp)
