# Try to find the GMP library
find_path(GMP_INCLUDE_DIR NAMES gmp.h
    PATHS /usr/include /usr/local/include /usr/include/x86_64-linux-gnu)

find_library(GMP_LIBRARY NAMES gmp
    PATHS /usr/lib /usr/local/lib /usr/lib/x86_64-linux-gnu)

if(GMP_INCLUDE_DIR AND GMP_LIBRARY)
    set(GMP_FOUND TRUE)
    set(GMP_INCLUDE_DIRS ${GMP_INCLUDE_DIR})
    set(GMP_LIBRARIES ${GMP_LIBRARY})
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMP
    REQUIRED_VARS GMP_LIBRARY GMP_INCLUDE_DIR)

mark_as_advanced(GMP_INCLUDE_DIR GMP_LIBRARY)