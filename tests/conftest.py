import pytest

# This will make pytest rewrite the asserts in `src/zktypes/` so that they
# print the values used in the assertions automatically.
pytest.register_assert_rewrite("zktypes")

