Directory for development database which is ignored by git.

Put a `.env` file into the `core` directory with the following content for 
Diesel CLI commands to use a Sqlite DB in this directory.

```shell
DATABASE_URL=db/database.sqlite3
```