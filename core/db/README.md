# Development Database

## Overview

Directory for development database which is ignored by git.

## Diesel

Put a `.env` file into the `core` directory with the following content for 
Diesel CLI commands to use a Sqlite DB in this directory.

```shell
DATABASE_URL=db/database.sqlite3
```

### Commands

Execute these command from the `core` directory.

- `diesel migration run`: create DB and run migrations
- `diesel migration redo`: roll back and rerun last migration. Make sure to
  execute this after adding a new migration to check that it can be rolled back.