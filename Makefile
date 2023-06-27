help: ## Display this help screen
	@grep -h \
		-E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | \
		awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-30s\033[0m %s\n", $$1, $$2}'

install-dev: # Install the Python packages for development
	pip3 install --user --break-system-packages --editable .[test,lint]

fmt: ## Format the code
	black .

lint: ## Check whether the code is formatted correctly
	black . --check
	flake8 .

type: ## Check the typing of the Python code
	MYPATH=src mypy .

test: ## Run tests
	pytest --doctest-modules


.PHONY: help install fmt lint test

